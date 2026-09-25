"""
Steganografi + IPFS + MetaMask + Google Giriş Sistemi
------------------------------------------------------

- MetaMask ile nonce + personal_sign doğrulaması
- WalletConnect ile imzalı giriş
- Google OAuth ile Gmail/Google hesabı girişi
- Google çıkışında uygulama oturumunun temizlenmesi
- Google hesabı tarayıcıda açık olsa bile
  uygulamaya otomatik giriş yapılmaması
- AES-256-GCM şifreleme
- Parolaya bağlı LSB steganografi
- Pinata / IPFS
- Admin ve kullanıcı engelleme sistemi
"""

from __future__ import annotations

import base64
import hashlib
import os
import random
import sqlite3
import time
import uuid

from contextlib import contextmanager
from io import BytesIO
from typing import Optional

import json as json_module
import html as html_module

import numpy as np
import requests
import streamlit as st
import streamlit.components.v1 as components

from streamlit_javascript import st_javascript

from PIL import Image

from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC

from eth_account import Account
from eth_account.messages import encode_defunct


# ==========================================================================
# YAPILANDIRMA
# ==========================================================================

def _get_secret(name: str) -> str:

    try:
        return st.secrets.get(name, "")
    except Exception:
        return ""


def _get_config_value(name: str) -> str:

    value = os.environ.get(name) or _get_secret(name)

    return value.strip() if value else ""


PINATA_API_KEY = _get_config_value(
    "PINATA_API_KEY"
)

PINATA_SECRET_KEY = _get_config_value(
    "PINATA_SECRET_KEY"
)

PINATA_ENDPOINT = (
    "https://api.pinata.cloud/pinning/pinFileToIPFS"
)

PINATA_GATEWAY_PREFIX = (
    "https://gateway.pinata.cloud/ipfs/"
)

PBKDF2_ITERATIONS = 200_000

SALT_LEN = 16

NONCE_LEN = 12

HEADER_BITS = 32


_ADMIN_WALLETS_RAW = _get_config_value(
    "ADMIN_WALLETS"
)

ADMIN_WALLETS = {
    addr.strip().lower()
    for addr in _ADMIN_WALLETS_RAW.split(",")
    if addr.strip()
}


DB_PATH = (
    os.environ.get("STEGO_DB_PATH")
    or "stego_app.db"
)


SUPABASE_DB_URL = _get_config_value(
    "SUPABASE_DB_URL"
)

USE_POSTGRES = bool(
    SUPABASE_DB_URL
)


if USE_POSTGRES:

    import psycopg2
    import psycopg2.extras


st.set_page_config(
    page_title="Steganografi + IPFS + MetaMask",
    page_icon="🔐",
    layout="wide"
)


# ==========================================================================
# VERİTABANI
# ==========================================================================

def _placeholder() -> str:

    return "%s" if USE_POSTGRES else "?"


@contextmanager
def _db():

    if USE_POSTGRES:

        conn = psycopg2.connect(
            SUPABASE_DB_URL
        )

    else:

        conn = sqlite3.connect(
            DB_PATH
        )

        conn.row_factory = sqlite3.Row

    try:

        yield conn

        conn.commit()

    finally:

        conn.close()


def _dict_cursor(conn):

    if USE_POSTGRES:

        return conn.cursor(
            cursor_factory=psycopg2.extras.RealDictCursor
        )

    return conn.cursor()


def init_db():

    global USE_POSTGRES

    try:

        with _db() as conn:

            cur = conn.cursor()

            if USE_POSTGRES:

                cur.execute("""
                    CREATE TABLE IF NOT EXISTS users (
                        wallet_address TEXT PRIMARY KEY,
                        first_seen DOUBLE PRECISION NOT NULL,
                        last_seen DOUBLE PRECISION NOT NULL,
                        is_banned BOOLEAN NOT NULL DEFAULT FALSE,
                        banned_reason TEXT
                    )
                """)

                cur.execute("""
                    CREATE TABLE IF NOT EXISTS activity_log (
                        id SERIAL PRIMARY KEY,
                        wallet_address TEXT NOT NULL,
                        action TEXT NOT NULL,
                        ipfs_hash TEXT,
                        success BOOLEAN NOT NULL,
                        timestamp DOUBLE PRECISION NOT NULL
                    )
                """)

            else:

                cur.execute("""
                    CREATE TABLE IF NOT EXISTS users (
                        wallet_address TEXT PRIMARY KEY,
                        first_seen REAL NOT NULL,
                        last_seen REAL NOT NULL,
                        is_banned INTEGER NOT NULL DEFAULT 0,
                        banned_reason TEXT
                    )
                """)

                cur.execute("""
                    CREATE TABLE IF NOT EXISTS activity_log (
                        id INTEGER PRIMARY KEY AUTOINCREMENT,
                        wallet_address TEXT NOT NULL,
                        action TEXT NOT NULL,
                        ipfs_hash TEXT,
                        success INTEGER NOT NULL,
                        timestamp REAL NOT NULL
                    )
                """)

    except Exception as exc:

        if USE_POSTGRES:

            st.warning(
                "Kalıcı veritabanına bağlanılamadı. "
                f"Geçici SQLite kullanılacak. Hata: {exc}"
            )

            USE_POSTGRES = False

            init_db()

            return

        raise

    # Eski veritabanlarına login_method ekle
    try:

        with _db() as conn:

            cur = conn.cursor()

            cur.execute(
                "ALTER TABLE users "
                "ADD COLUMN login_method TEXT DEFAULT 'metamask'"
            )

    except Exception:

        pass


def upsert_user(
    user_id: str,
    login_method: str = "metamask"
):

    user_id = user_id.lower()

    now = time.time()

    ph = _placeholder()

    banned_default = (
        "FALSE"
        if USE_POSTGRES
        else "0"
    )

    with _db() as conn:

        cur = conn.cursor()

        cur.execute(
            f"""
            INSERT INTO users
            (
                wallet_address,
                first_seen,
                last_seen,
                is_banned,
                login_method
            )
            VALUES
            (
                {ph},
                {ph},
                {ph},
                {banned_default},
                {ph}
            )

            ON CONFLICT (wallet_address)
            DO UPDATE SET
                last_seen = EXCLUDED.last_seen,
                login_method = EXCLUDED.login_method
            """,
            (
                user_id,
                now,
                now,
                login_method
            )
        )


def is_wallet_banned(
    wallet_address: str
) -> bool:

    wallet_address = wallet_address.lower()

    ph = _placeholder()

    with _db() as conn:

        cur = _dict_cursor(conn)

        cur.execute(
            f"""
            SELECT is_banned
            FROM users
            WHERE wallet_address = {ph}
            """,
            (wallet_address,)
        )

        row = cur.fetchone()

    return bool(
        row and row["is_banned"]
    )


def set_wallet_banned(
    wallet_address: str,
    banned: bool,
    reason: str = ""
):

    wallet_address = wallet_address.lower()

    ph = _placeholder()

    banned_value = (
        banned
        if USE_POSTGRES
        else (1 if banned else 0)
    )

    with _db() as conn:

        cur = conn.cursor()

        cur.execute(
            f"""
            UPDATE users
            SET
                is_banned = {ph},
                banned_reason = {ph}
            WHERE wallet_address = {ph}
            """,
            (
                banned_value,
                reason,
                wallet_address
            )
        )


def is_admin_wallet(
    wallet_address: str
) -> bool:

    return (
        bool(wallet_address)
        and
        wallet_address.lower()
        in ADMIN_WALLETS
    )


def log_action(
    user_id: str,
    action: str,
    ipfs_hash: str = "",
    success: bool = True
):

    ph = _placeholder()

    success_value = (
        success
        if USE_POSTGRES
        else (1 if success else 0)
    )

    with _db() as conn:

        cur = conn.cursor()

        cur.execute(
            f"""
            INSERT INTO activity_log
            (
                wallet_address,
                action,
                ipfs_hash,
                success,
                timestamp
            )
            VALUES
            (
                {ph},
                {ph},
                {ph},
                {ph},
                {ph}
            )
            """,
            (
                user_id.lower(),
                action,
                ipfs_hash,
                success_value,
                time.time()
            )
        )


def list_users():

    with _db() as conn:

        cur = _dict_cursor(conn)

        cur.execute(
            "SELECT * FROM users ORDER BY last_seen DESC"
        )

        return cur.fetchall()


def list_recent_activity(
    limit: int = 100
):

    ph = _placeholder()

    with _db() as conn:

        cur = _dict_cursor(conn)

        cur.execute(
            f"""
            SELECT *
            FROM activity_log
            ORDER BY timestamp DESC
            LIMIT {ph}
            """,
            (limit,)
        )

        return cur.fetchall()


init_db()


# ==========================================================================
# GOOGLE / OTURUM YARDIMCI FONKSİYONLARI
# ==========================================================================

def _get_streamlit_user():

    """
    Streamlit sürümüne göre st.user veya experimental_user.
    """

    return (
        getattr(st, "user", None)
        or
        getattr(
            st,
            "experimental_user",
            None
        )
    )


def _google_auth_configured() -> bool:

    try:

        return bool(
            st.secrets
            .get("auth", {})
            .get("client_id")
        )

    except Exception:

        return False


def _clear_application_auth_state():

    """
    Sadece uygulamamızdaki oturum bilgilerini temizler.
    """

    keys_to_remove = [

        "authenticated",

        "user_id",

        "login_method",

        "display_name",

        "auth_nonce",

        "login_attempt",

        "wc_check_attempt",

        "google_login_started",

    ]

    for key in keys_to_remove:

        st.session_state.pop(
            key,
            None
        )


# ==========================================================================
# METAMASK
# ==========================================================================

def _new_nonce() -> str:

    return uuid.uuid4().hex


def _login_message(
    nonce: str
) -> str:

    return (
        "Steganografi + IPFS uygulamasına giriş yapıyorsunuz.\n"
        f"Nonce: {nonce}\n"
        "Bu imza yalnızca kimliğinizi doğrulamak için kullanılır, "
        "herhangi bir işlem/transfer başlatmaz."
    )


def verify_signature(
    message: str,
    signature: str,
    expected_address: str
) -> bool:

    try:

        encoded = encode_defunct(
            text=message
        )

        recovered = Account.recover_message(
            encoded,
            signature=signature
        )

        return (
            recovered.lower()
            ==
            expected_address.lower()
        )

    except Exception:

        return False


def _build_metamask_js(
    message: str
) -> str:

    message_js = json_module.dumps(
        message
    )

    return f"""
    (async () => {{

        try {{

            const provider =
                (window.top && window.top.ethereum)
                ? window.top.ethereum
                : window.ethereum;

            if (!provider) {{

                return JSON.stringify({{
                    error:
                    "MetaMask bulunamadı. Lütfen tarayıcı eklentisini kurun."
                }});

            }}

            const accounts =
                await provider.request({{
                    method: 'eth_requestAccounts'
                }});

            const address = accounts[0];

            const signature =
                await provider.request({{
                    method: 'personal_sign',
                    params: [{message_js}, address]
                }});

            return JSON.stringify({{
                address: address,
                signature: signature
            }});

        }} catch (err) {{

            return JSON.stringify({{
                error:
                (err && err.message)
                ? err.message
                : String(err)
            }});

        }}

    }})()
    """


def _complete_login(
    user_id: str,
    login_method: str,
    display_name: Optional[str] = None
):

    user_id = user_id.lower()

    upsert_user(
        user_id,
        login_method
    )

    if is_wallet_banned(
        user_id
    ):

        st.error(
            "Bu hesap yönetici tarafından engellenmiştir. "
            "Erişiminiz yok."
        )

        st.session_state[
            "auth_nonce"
        ] = _new_nonce()

        st.session_state[
            "login_attempt"
        ] = 0

        return

    st.session_state[
        "authenticated"
    ] = True

    st.session_state[
        "user_id"
    ] = user_id

    st.session_state[
        "login_method"
    ] = login_method

    st.session_state[
        "display_name"
    ] = (
        display_name
        or
        user_id
    )

    # Google OAuth giriş işlemi tamamlandı.
    st.session_state[
        "google_login_started"
    ] = False

    st.rerun()


def current_user_is_admin() -> bool:

    return (
        st.session_state.get(
            "authenticated",
            False
        )

        and

        st.session_state.get(
            "login_method"
        )
        ==
        "metamask"

        and

        is_admin_wallet(
            st.session_state.get(
                "user_id",
                ""
            )
        )
    )


def render_metamask_login():

    nonce = st.session_state[
        "auth_nonce"
    ]

    message = _login_message(
        nonce
    )

    st.caption(
        "Cüzdanınızla bağlanıp bir imza isteğini onaylayın. "
        "Ücret gerektirmez."
    )

    if "login_attempt" not in st.session_state:

        st.session_state[
            "login_attempt"
        ] = 0

    if st.button(
        "🦊 MetaMask ile Bağlan & İmzala",
        type="primary",
        key="mm_btn"
    ):

        st.session_state[
            "login_attempt"
        ] += 1

    if st.session_state[
        "login_attempt"
    ] > 0:

        js_code = _build_metamask_js(
            message
        )

        with st.spinner(
            "MetaMask'ta bağlantı ve imza isteğini onaylayın..."
        ):

            result = st_javascript(
                js_code,
                key=(
                    "metamask_login_"
                    f"{st.session_state['login_attempt']}"
                )
            )

        if result and result != 0:

            try:

                payload = json_module.loads(
                    result
                )

            except (
                TypeError,
                ValueError
            ):

                payload = {
                    "error":
                    "Beklenmeyen bir yanıt alındı."
                }

            if "error" in payload:

                st.error(
                    payload["error"]
                )

            elif (
                payload.get("address")
                and
                payload.get("signature")
            ):

                wallet_address = (
                    payload["address"]
                )

                if verify_signature(
                    message,
                    payload["signature"],
                    wallet_address
                ):

                    _complete_login(
                        wallet_address,
                        "metamask",
                        display_name=wallet_address
                    )

                else:

                    st.error(
                        "İmza doğrulanamadı. "
                        "Lütfen tekrar deneyin."
                    )

                    st.session_state[
                        "auth_nonce"
                    ] = _new_nonce()


# ==========================================================================
# WALLETCONNECT
# ==========================================================================

def _build_walletconnect_html(
    message: str,
    project_id: str
) -> str:

    message_js = json_module.dumps(
        message
    )

    project_id_js = json_module.dumps(
        project_id
    )

    return f"""

    <div style="font-family:sans-serif;">

      <button
        id="wcConnectBtn"
        style="
          background:#3396FF;
          color:white;
          border:none;
          padding:12px 20px;
          border-radius:8px;
          font-size:15px;
          cursor:pointer;
        "
      >
        🔗 WalletConnect ile Bağlan &amp; İmzala
      </button>

      <p
        id="wcStatus"
        style="
          margin-top:10px;
          color:#555;
          font-size:14px;
        "
      ></p>

    </div>

    <script>

    async function wcConnect() {{

        const statusEl =
            document.getElementById(
                'wcStatus'
            );

        try {{

            statusEl.innerText =
                'Kütüphane yükleniyor...';

            if (!window.EthereumProvider) {{

                await new Promise(
                    (resolve, reject) => {{

                        const s =
                            document.createElement(
                                'script'
                            );

                        s.src =
                            'https://cdn.jsdelivr.net/npm/@walletconnect/ethereum-provider@2/dist/index.umd.js';

                        s.onload = resolve;

                        s.onerror = () =>
                            reject(
                                new Error(
                                    'WalletConnect kütüphanesi yüklenemedi.'
                                )
                            );

                        document.head.appendChild(s);

                    }}
                );

            }}

            const provider =
                await window.EthereumProvider.init({{

                    projectId:
                        {project_id_js},

                    chains: [1],

                    showQrModal: true,

                    metadata: {{

                        name:
                            'Steganografi + IPFS Uygulaması',

                        description:
                            'Steganografi + IPFS uygulamasına giriş',

                        url:
                            window.location.origin,

                        icons: []

                    }}

                }});

            statusEl.innerText =
                'Lütfen açılan pencereden cüzdanınızı seçip bağlanın...';

            await provider.connect();

            const address =
                provider.accounts[0];

            statusEl.innerText =
                'Bağlandı! Lütfen cüzdanınızda imza isteğini onaylayın...';

            const signature =
                await provider.request({{

                    method:
                        'personal_sign',

                    params:
                        [{message_js}, address]

                }});

            localStorage.setItem(
                'wc_login_result',
                JSON.stringify({{
                    address: address,
                    signature: signature
                }})
            );

            statusEl.innerText =
                '✅ Bağlandı! Şimdi aşağıdaki "Girişi Tamamla" butonuna tıklayın.';

        }} catch (err) {{

            const errMsg =
                (err && err.message)
                ? err.message
                : String(err);

            statusEl.innerText =
                'Hata: ' + errMsg;

            localStorage.setItem(
                'wc_login_result',
                JSON.stringify({{
                    error: errMsg
                }})
            );

        }}

    }}

    document
        .getElementById('wcConnectBtn')
        .addEventListener(
            'click',
            wcConnect
        );

    </script>
    """


def render_walletconnect_login():

    nonce = st.session_state[
        "auth_nonce"
    ]

    message = _login_message(
        nonce
    )

    project_id = _get_config_value(
        "WALLETCONNECT_PROJECT_ID"
    )

    if not project_id:

        st.info(
            "WalletConnect'i etkinleştirmek için "
            "WALLETCONNECT_PROJECT_ID tanımlayın."
        )

        return

    st.caption(
        "Trust Wallet, Coinbase Wallet, Rabby, "
        "Binance Wallet ve diğer cüzdanlarla bağlanabilirsiniz."
    )

    html_code = _build_walletconnect_html(
        message,
        project_id
    )

    components.html(
        html_code,
        height=200
    )

    if "wc_check_attempt" not in st.session_state:

        st.session_state[
            "wc_check_attempt"
        ] = 0

    if st.button(
        "✅ Girişi Tamamla",
        key="wc_finish_btn"
    ):

        st.session_state[
            "wc_check_attempt"
        ] += 1

        result = st_javascript(
            "localStorage.getItem('wc_login_result')",
            key=(
                "wc_read_"
                f"{st.session_state['wc_check_attempt']}"
            )
        )

        if not result or result == 0:

            st.warning(
                "Henüz bir bağlantı bulunamadı."
            )

            return

        try:

            payload = json_module.loads(
                result
            )

        except (
            TypeError,
            ValueError
        ):

            payload = {
                "error":
                "Beklenmeyen bir yanıt alındı."
            }

        if "error" in payload:

            st.error(
                payload["error"]
            )

        elif (
            payload.get("address")
            and
            payload.get("signature")
        ):

            wallet_address = (
                payload["address"]
            )

            if verify_signature(
                message,
                payload["signature"],
                wallet_address
            ):

                _complete_login(
                    wallet_address,
                    "walletconnect",
                    display_name=wallet_address
                )

            else:

                st.error(
                    "İmza doğrulanamadı."
                )


# ==========================================================================
# GOOGLE GİRİŞ
# ==========================================================================

def render_google_login():

    if not _google_auth_configured():

        st.info(
            "Google girişini etkinleştirmek için "
            "secrets.toml içindeki [auth] ayarlarını kontrol edin."
        )

        return

    st.caption(
        "Google hesabınızla tek tıkla giriş yapın."
    )

    if st.button(
        "📧 Gmail ile Giriş Yap",
        type="primary",
        key="google_btn"
    ):

        # --------------------------------------------------------------
        # KRİTİK:
        #
        # Google ile giriş işlemi SADECE kullanıcı butona bastığında
        # başlatılır.
        # --------------------------------------------------------------

        st.session_state[
            "google_login_started"
        ] = True

        st.login()


# ==========================================================================
# KİMLİK DOĞRULAMA
# ==========================================================================

def ensure_authenticated() -> bool:

    # --------------------------------------------------------------
    # SESSION STATE İLK DEĞERLERİ
    # --------------------------------------------------------------

    if "auth_nonce" not in st.session_state:

        st.session_state[
            "auth_nonce"
        ] = _new_nonce()

    if "authenticated" not in st.session_state:

        st.session_state[
            "authenticated"
        ] = False

    if "user_id" not in st.session_state:

        st.session_state[
            "user_id"
        ] = None

    if "login_method" not in st.session_state:

        st.session_state[
            "login_method"
        ] = None

    if "display_name" not in st.session_state:

        st.session_state[
            "display_name"
        ] = None

    if "google_login_started" not in st.session_state:

        st.session_state[
            "google_login_started"
        ] = False

    # --------------------------------------------------------------
    # GOOGLE OTURUMU
    # --------------------------------------------------------------

    streamlit_user = _get_streamlit_user()

    google_login_started = (
        st.session_state.get(
            "google_login_started",
            False
        )
    )

    # --------------------------------------------------------------
    # KRİTİK KURAL
    #
    # Google hesabı tarayıcıda açık olabilir.
    #
    # Fakat kullanıcı bu uygulamada:
    #
    # "📧 Gmail ile Giriş Yap"
    #
    # butonuna BASMADAN Google hesabını uygulama oturumu
    # olarak kabul etmiyoruz.
    # --------------------------------------------------------------

    if (
        google_login_started
        and
        streamlit_user is not None
        and
        getattr(
            streamlit_user,
            "is_logged_in",
            False
        )
        and
        not st.session_state.get(
            "authenticated",
            False
        )
    ):

        google_id = (
            getattr(
                streamlit_user,
                "email",
                None
            )
            or
            getattr(
                streamlit_user,
                "sub",
                ""
            )
            or
            ""
        )

        if google_id:

            _complete_login(
                google_id,
                "google",
                display_name=(
                    getattr(
                        streamlit_user,
                        "name",
                        None
                    )
                    or
                    google_id
                )
            )

    # --------------------------------------------------------------
    # GİRİŞ YAPILMADIYSA GİRİŞ EKRANI
    # --------------------------------------------------------------

    if not st.session_state.get(
        "authenticated",
        False
    ):

        st.title(
            "🔐 Giriş Gerekli"
        )

        st.write(
            "Uygulamayı kullanmak için "
            "aşağıdaki yöntemlerden biriyle giriş yapın."
        )

        tab_google, tab_metamask, tab_wc = st.tabs(
            [
                "📧 Gmail",
                "🦊 MetaMask",
                "🔗 WalletConnect"
            ]
        )

        with tab_google:

            render_google_login()

        with tab_metamask:

            render_metamask_login()

        with tab_wc:

            render_walletconnect_login()

        return False

    return True


# ==========================================================================
# AES-256-GCM
# ==========================================================================

def derive_key(
    password: str,
    salt: bytes
) -> bytes:

    kdf = PBKDF2HMAC(
        algorithm=hashes.SHA256(),
        length=32,
        salt=salt,
        iterations=PBKDF2_ITERATIONS
    )

    return kdf.derive(
        password.encode("utf-8")
    )


def encrypt_message(
    password: str,
    plaintext: str
) -> bytes:

    salt = os.urandom(
        SALT_LEN
    )

    nonce = os.urandom(
        NONCE_LEN
    )

    key = derive_key(
        password,
        salt
    )

    ciphertext = AESGCM(
        key
    ).encrypt(
        nonce,
        plaintext.encode("utf-8"),
        None
    )

    return (
        salt
        + nonce
        + ciphertext
    )


def decrypt_message(
    password: str,
    blob: bytes
) -> str:

    salt = blob[
        :SALT_LEN
    ]

    nonce = blob[
        SALT_LEN:
        SALT_LEN + NONCE_LEN
    ]

    ciphertext = blob[
        SALT_LEN + NONCE_LEN:
    ]

    key = derive_key(
        password,
        salt
    )

    plaintext = AESGCM(
        key
    ).decrypt(
        nonce,
        ciphertext,
        None
    )

    return plaintext.decode(
        "utf-8"
    )


# ==========================================================================
# LSB STEGANOGRAFİ
# ==========================================================================

def _scrambled_positions(
    password: str,
    total_positions: int,
    count: int
) -> list[int]:

    seed = int.from_bytes(
        hashlib.sha256(
            password.encode("utf-8")
        ).digest(),
        "big"
    )

    rng = random.Random(
        seed
    )

    positions = list(
        range(total_positions)
    )

    rng.shuffle(
        positions
    )

    if count > total_positions:

        raise ValueError(
            "Resim, bu kadar veriyi gizlemek için yeterli kapasiteye sahip değil."
        )

    return positions[
        :count
    ]


def _bytes_to_bits(
    data: bytes
) -> list[int]:

    bits = []

    for byte in data:

        bits.extend(
            (byte >> i) & 1
            for i in range(
                7,
                -1,
                -1
            )
        )

    return bits


def _bits_to_bytes(
    bits: list[int]
) -> bytes:

    out = bytearray()

    for i in range(
        0,
        len(bits),
        8
    ):

        byte_bits = bits[
            i:i + 8
        ]

        value = 0

        for b in byte_bits:

            value = (
                value << 1
            ) | b

        out.append(
            value
        )

    return bytes(out)


def embed_data_in_image(
    image: Image.Image,
    password: str,
    plaintext: str
) -> Image.Image:

    encrypted_blob = encrypt_message(
        password,
        plaintext
    )

    payload_len = len(
        encrypted_blob
    )

    rgb_image = image.convert(
        "RGB"
    )

    channel_array = np.array(
        rgb_image,
        dtype=np.uint8
    ).flatten()

    total_positions = (
        channel_array.size
    )

    header_bits = [
        (
            payload_len >> i
        ) & 1
        for i in range(
            HEADER_BITS - 1,
            -1,
            -1
        )
    ]

    payload_bits = _bytes_to_bits(
        encrypted_blob
    )

    all_bits = (
        header_bits
        +
        payload_bits
    )

    positions = _scrambled_positions(
        password,
        total_positions,
        len(all_bits)
    )

    for pos, bit in zip(
        positions,
        all_bits
    ):

        channel_array[pos] = (
            channel_array[pos] & 0xFE
        ) | bit

    new_array = channel_array.reshape(
        np.array(rgb_image).shape
    )

    return Image.fromarray(
        new_array,
        mode="RGB"
    )


def extract_data_from_image(
    image: Image.Image,
    password: str
) -> str:

    rgb_image = image.convert(
        "RGB"
    )

    channel_array = np.array(
        rgb_image,
        dtype=np.uint8
    ).flatten()

    total_positions = (
        channel_array.size
    )

    header_positions = _scrambled_positions(
        password,
        total_positions,
        HEADER_BITS
    )

    header_bits = [
        int(channel_array[p] & 1)
        for p in header_positions
    ]

    payload_len = 0

    for b in header_bits:

        payload_len = (
            payload_len << 1
        ) | b

    if (
        payload_len <= 0
        or
        payload_len > total_positions
    ):

        raise ValueError(
            "Bu resimde geçerli bir gizli veri bulunamadı "
            "(ya da parola hatalı)."
        )

    total_bits_needed = (
        HEADER_BITS
        +
        payload_len * 8
    )

    all_positions = _scrambled_positions(
        password,
        total_positions,
        total_bits_needed
    )

    payload_positions = (
        all_positions[
            HEADER_BITS:
        ]
    )

    payload_bits = [
        int(channel_array[p] & 1)
        for p in payload_positions
    ]

    encrypted_blob = _bits_to_bytes(
        payload_bits
    )

    try:

        return decrypt_message(
            password,
            encrypted_blob
        )

    except Exception:

        raise ValueError(
            "Veri çözülemedi. "
            "Parola yanlış olabilir veya resim bozulmuş olabilir."
        )


# ==========================================================================
# PINATA / IPFS
# ==========================================================================

def upload_to_pinata(
    image: Image.Image
) -> Optional[str]:

    if (
        not PINATA_API_KEY
        or
        not PINATA_SECRET_KEY
    ):

        st.error(
            "Pinata API anahtarları tanımlı değil."
        )

        return None

    buffer = BytesIO()

    image.save(
        buffer,
        format="PNG"
    )

    files = {
        "file": (
            "stego_image.png",
            buffer.getvalue()
        )
    }

    headers = {
        "pinata_api_key":
            PINATA_API_KEY,

        "pinata_secret_api_key":
            PINATA_SECRET_KEY
    }

    try:

        response = requests.post(
            PINATA_ENDPOINT,
            files=files,
            headers=headers,
            timeout=30
        )

        response.raise_for_status()

    except requests.RequestException as exc:

        st.error(
            f"Pinata'ya yükleme sırasında hata oluştu: {exc}"
        )

        return None

    return response.json().get(
        "IpfsHash"
    )


def fetch_from_pinata(
    ipfs_hash: str
) -> Optional[Image.Image]:

    try:

        response = requests.get(
            f"{PINATA_GATEWAY_PREFIX}{ipfs_hash}",
            timeout=30
        )

        response.raise_for_status()

    except requests.RequestException as exc:

        st.error(
            f"IPFS'ten resim alınırken hata oluştu: {exc}"
        )

        return None

    return Image.open(
        BytesIO(
            response.content
        )
    )


# ==========================================================================
# KOPYALAMA BUTONU
# ==========================================================================

def render_copy_button(
    text_to_copy: str,
    label: str = "📋 IPFS Kodunu Kopyala"
):

    safe_text = html_module.escape(
        text_to_copy
    )

    safe_label = html_module.escape(
        label
    )

    html_code = f"""

    <div style="font-family:sans-serif;">

      <input
        type="text"
        value="{safe_text}"
        id="copyInput"
        readonly
        style="
          position:absolute;
          left:-9999px;
        "
      >

      <button
        onclick="copyToClipboard()"
        style="
          background:#4CAF50;
          color:white;
          border:none;
          padding:8px 18px;
          border-radius:6px;
          font-size:14px;
          cursor:pointer;
        "
      >
        {safe_label}
      </button>

      <span
        id="copyStatus"
        style="
          margin-left:10px;
          color:#555;
          font-size:13px;
        "
      ></span>

    </div>

    <script>

    function copyToClipboard() {{

        const input =
            document.getElementById(
                'copyInput'
            );

        input.select();

        input.setSelectionRange(
            0,
            99999
        );

        try {{

            document.execCommand(
                'copy'
            );

            document.getElementById(
                'copyStatus'
            ).innerText =
                'Kopyalandı ✓';

        }} catch (err) {{

            document.getElementById(
                'copyStatus'
            ).innerText =
                'Kopyalanamadı.';

        }}

    }}

    </script>
    """

    components.html(
        html_code,
        height=50
    )


# ==========================================================================
# MESAJ GİZLE
# ==========================================================================

def render_encode_screen():

    st.subheader(
        "📥 Mesajı Resme Gizle"
    )

    col_input, col_output = st.columns(
        2
    )

    file = col_input.file_uploader(
        "Kapak resmi yükleyin (PNG önerilir)",
        type=[
            "png",
            "jpg",
            "jpeg"
        ]
    )

    if not file:

        col_input.info(
            "Lütfen bir resim yükleyin."
        )

        return

    image = Image.open(
        BytesIO(
            file.getvalue()
        )
    )

    col_input.image(
        image,
        caption="Kapak resmi",
        use_container_width=True
    )

    capacity_bits = np.array(
        image.convert("RGB")
    ).size

    max_payload_bytes = max(
        (
            capacity_bits
            - HEADER_BITS
        ) // 8
        - (
            SALT_LEN
            + NONCE_LEN
            + 16
        ),
        0
    )

    col_input.caption(
        "Yaklaşık maksimum mesaj kapasitesi: "
        f"~{max_payload_bytes} karakter"
    )

    message = col_input.text_area(
        "Gizlenecek mesaj"
    )

    password = col_input.text_input(
        "Şifreleme parolası",
        type="password"
    )

    if col_input.button(
        "🔒 Şifrele, Gizle ve IPFS'e Yükle",
        type="primary"
    ):

        if not message:

            col_input.error(
                "Mesaj boş olamaz."
            )

            return

        if not password:

            col_input.error(
                "Lütfen bir parola girin."
            )

            return

        try:

            with st.spinner(
                "Mesaj şifreleniyor ve resme gömülüyor..."
            ):

                stego_image = embed_data_in_image(
                    image,
                    password,
                    message
                )

        except ValueError as exc:

            col_input.error(
                str(exc)
            )

            return

        with st.spinner(
            "IPFS'e yükleniyor..."
        ):

            ipfs_hash = upload_to_pinata(
                stego_image
            )

        if not ipfs_hash:

            col_output.error(
                "Resim IPFS'e yüklenirken hata oluştu."
            )

            return

        log_action(
            st.session_state.get(
                "user_id",
                ""
            ),
            "encode",
            ipfs_hash,
            success=True
        )

        col_output.success(
            "Mesaj başarıyla gizlendi ve IPFS'e yüklendi."
        )

        col_output.code(
            ipfs_hash,
            language=None
        )

        with col_output:

            render_copy_button(
                ipfs_hash
            )


# ==========================================================================
# MESAJ ÇÖZ
# ==========================================================================

def render_decode_screen():

    st.subheader(
        "📤 Resimden Mesajı Çöz"
    )

    ipfs_hash = st.text_input(
        "IPFS Hash"
    )

    password = st.text_input(
        "Şifreleme parolası",
        type="password"
    )

    if st.button(
        "🔓 Çöz",
        type="primary"
    ):

        if (
            not ipfs_hash
            or
            not password
        ):

            st.error(
                "IPFS hash ve parola gereklidir."
            )

            return

        with st.spinner(
            "Resim IPFS'ten indiriliyor..."
        ):

            image = fetch_from_pinata(
                ipfs_hash
            )

        if image is None:

            st.error(
                "Hatalı IPFS hash."
            )

            log_action(
                st.session_state.get(
                    "user_id",
                    ""
                ),
                "decode",
                ipfs_hash,
                success=False
            )

            return

        try:

            with st.spinner(
                "Veri çözülüyor..."
            ):

                message = extract_data_from_image(
                    image,
                    password
                )

        except ValueError as exc:

            st.error(
                str(exc)
            )

            log_action(
                st.session_state.get(
                    "user_id",
                    ""
                ),
                "decode",
                ipfs_hash,
                success=False
            )

            return

        log_action(
            st.session_state.get(
                "user_id",
                ""
            ),
            "decode",
            ipfs_hash,
            success=True
        )

        st.success(
            "Mesaj başarıyla çözüldü:"
        )

        st.text_area(
            "Çözülen mesaj",
            value=message,
            height=150
        )

        st.image(
            image,
            caption="Kaynak resim",
            use_container_width=True
        )


# ==========================================================================
# SIDEBAR HESAP
# ==========================================================================

def render_sidebar_account():

    user_id = st.session_state.get(
        "user_id",
        ""
    )

    method = st.session_state.get(
        "login_method",
        ""
    )

    display_name = (
        st.session_state.get(
            "display_name"
        )
        or
        user_id
    )

    method_label = {

        "metamask":
            "🦊 MetaMask",

        "walletconnect":
            "🔗 WalletConnect",

        "google":
            "📧 Google"

    }.get(
        method,
        method
    )

    if current_user_is_admin():

        st.sidebar.success(
            f"👑 Yönetici ({method_label}):\n"
            f"`{display_name}`"
        )

    else:

        st.sidebar.success(
            f"{method_label} ile giriş:\n"
            f"`{display_name}`"
        )

    # --------------------------------------------------------------
    # ÇIKIŞ
    # --------------------------------------------------------------

    if st.sidebar.button(
        "Çıkış yap",
        key="logout_button"
    ):

        was_google = (
            method == "google"
        )

        # ----------------------------------------------------------
        # Önce uygulamanın kendi session state'ini temizle.
        # ----------------------------------------------------------

        _clear_application_auth_state()

        # ----------------------------------------------------------
        # Google girişiyse Streamlit OIDC oturumunu kapat.
        # ----------------------------------------------------------

        if was_google:

            try:

                st.logout()

            except Exception:

                pass

        # ----------------------------------------------------------
        # Giriş ekranına dön.
        # ----------------------------------------------------------

        st.rerun()


# ==========================================================================
# ADMIN
# ==========================================================================

def render_admin_panel():

    st.subheader(
        "👑 Yönetici Paneli"
    )

    users = list_users()

    st.markdown(
        f"**Toplam kullanıcı:** {len(users)}"
    )

    method_label = {

        "metamask":
            "🦊 MetaMask",

        "walletconnect":
            "🔗 WalletConnect",

        "google":
            "📧 Google"

    }

    st.markdown(
        "### Kullanıcılar"
    )

    for user in users:

        user_id = user[
            "wallet_address"
        ]

        login_method = (
            user["login_method"]
            or
            "metamask"
        )

        is_self_admin = (
            login_method == "metamask"
            and
            is_admin_wallet(
                user_id
            )
        )

        cols = st.columns(
            [
                3,
                1,
                2,
                2,
                2
            ]
        )

        cols[0].code(
            user_id,
            language=None
        )

        cols[1].caption(
            method_label.get(
                login_method,
                login_method
            )
        )

        cols[2].caption(
            "İlk görülme: "
            +
            time.strftime(
                "%Y-%m-%d %H:%M",
                time.localtime(
                    user["first_seen"]
                )
            )
        )

        cols[3].caption(
            "Son görülme: "
            +
            time.strftime(
                "%Y-%m-%d %H:%M",
                time.localtime(
                    user["last_seen"]
                )
            )
        )

        if is_self_admin:

            cols[4].caption(
                "👑 Yönetici (engellenemez)"
            )

        elif user["is_banned"]:

            if cols[4].button(
                "Engeli Kaldır",
                key=f"unban_{user_id}"
            ):

                set_wallet_banned(
                    user_id,
                    False
                )

                st.rerun()

        else:

            if cols[4].button(
                "Engelle",
                key=f"ban_{user_id}"
            ):

                set_wallet_banned(
                    user_id,
                    True,
                    reason="Yönetici tarafından engellendi"
                )

                st.rerun()

    st.divider()

    st.markdown(
        "### Son İşlemler"
    )

    activity = list_recent_activity(
        limit=100
    )

    if not activity:

        st.caption(
            "Henüz işlem kaydı yok."
        )

    else:

        st.dataframe(
            [
                {
                    "Zaman":
                        time.strftime(
                            "%Y-%m-%d %H:%M:%S",
                            time.localtime(
                                a["timestamp"]
                            )
                        ),

                    "Kullanıcı":
                        a["wallet_address"],

                    "İşlem":
                        a["action"],

                    "IPFS Hash":
                        a["ipfs_hash"] or "-",

                    "Başarılı mı":
                        "✅"
                        if a["success"]
                        else "❌"
                }

                for a in activity
            ],

            use_container_width=True,

            hide_index=True
        )

    st.caption(
        "Parolalar ve gizlenen mesaj içerikleri "
        "veritabanında tutulmaz."
    )


# ==========================================================================
# ANA PROGRAM
# ==========================================================================

def main():

    if not ensure_authenticated():

        return

    user_id = st.session_state.get(
        "user_id",
        ""
    )

    # --------------------------------------------------------------
    # Kullanıcı ban kontrolü
    # --------------------------------------------------------------

    if is_wallet_banned(
        user_id
    ):

        st.error(
            "Bu hesap yönetici tarafından engellenmiştir. "
            "Oturumunuz kapatılıyor."
        )

        _clear_application_auth_state()

        st.stop()

    # --------------------------------------------------------------
    # ANA UYGULAMA
    # --------------------------------------------------------------

    st.title(
        "🔐 Steganografi Bilimine Yeni Bir Boyut"
    )

    render_sidebar_account()

    tab_options = [
        "Mesaj Gizle",
        "Mesaj Çöz"
    ]

    if current_user_is_admin():

        tab_options.append(
            "Yönetici Paneli"
        )

    tab = st.sidebar.radio(
        "İşlem seçin",
        tab_options
    )

    if tab == "Mesaj Gizle":

        render_encode_screen()

    elif tab == "Mesaj Çöz":

        render_decode_screen()

    else:

        render_admin_panel()


# ==========================================================================
# BAŞLAT
# ==========================================================================

if __name__ == "__main__":

    main()
