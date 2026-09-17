#!/bin/bash
# Nefarious Hub Termux Launcher v1.4.5
set -e

REPO="${NEF_REPO:-relayced/test-nef}"
export NEF_REPO="$REPO"
BRANCH="main"
BASE_URL="https://raw.githubusercontent.com/$REPO/$BRANCH"
VERSION_URL="$BASE_URL/version.txt"
BIN_DIR="${HOME:-.}"
LOCAL_BIN="$BIN_DIR/nefhub"

# ANSI Colors
CYAN='\033[38;5;75m'
GREEN='\033[38;5;78m'
AMBER='\033[38;5;214m'
RED='\033[38;5;203m'
GRAY='\033[38;5;244m'
NC='\033[0m'
BOLD='\033[1m'

# Auto-detect terminal width & calculate dynamic horizontal centering
# Handles interactive terminal as well as piped execution (curl ... | bash)
detect_terminal_geometry() {
    local sz=""
    local c=""
    local r=""

    # 1. Try stty size on /dev/tty (controlling terminal device in Termux)
    if [ -e /dev/tty ]; then
        sz=$(stty size < /dev/tty 2>/dev/null || true)
        if [ -z "$sz" ]; then
            sz=$(/system/bin/stty size < /dev/tty 2>/dev/null || true)
        fi
    fi

    # 2. Try stty size on stdout (fd 1) or stderr (fd 2) - unpiped terminal descriptors
    if [ -z "$sz" ]; then
        sz=$(stty size <&1 2>/dev/null || stty size <&2 2>/dev/null || true)
    fi
    if [ -z "$sz" ]; then
        sz=$(/system/bin/stty size <&1 2>/dev/null || /system/bin/stty size <&2 2>/dev/null || true)
    fi

    # 3. Try stty size directly on stdin
    if [ -z "$sz" ]; then
        sz=$(stty size 2>/dev/null || true)
    fi

    if [ -n "$sz" ]; then
        set -- $sz
        r="$1"
        c="$2"
        if [ -n "$c" ] && [ "$c" -gt 0 ] 2>/dev/null; then
            echo "$c ${r:-24}"
            return
        fi
    fi

    # 4. Try tput cols with /dev/tty, fd 1, or default
    if [ -e /dev/tty ]; then
        c=$(tput cols < /dev/tty 2>/dev/null || true)
        r=$(tput lines < /dev/tty 2>/dev/null || true)
    fi
    if [ -z "$c" ] || [ "$c" -le 0 ] 2>/dev/null; then
        c=$(tput cols <&1 2>/dev/null || tput cols 2>/dev/null || true)
        r=$(tput lines <&1 2>/dev/null || tput lines 2>/dev/null || true)
    fi
    if [ -n "$c" ] && [ "$c" -gt 0 ] 2>/dev/null; then
        echo "$c ${r:-24}"
        return
    fi

    # 5. Try stty -a parsing
    local raw=""
    if [ -e /dev/tty ]; then
        raw=$(stty -a < /dev/tty 2>/dev/null || true)
    fi
    if [ -z "$raw" ]; then
        raw=$(stty -a <&1 2>/dev/null || stty -a 2>/dev/null || true)
    fi
    if [ -n "$raw" ]; then
        c=$(echo "$raw" | grep -o 'columns [0-9]\+' | head -n 1 | awk '{print $2}' || true)
        r=$(echo "$raw" | grep -o 'rows [0-9]\+' | head -n 1 | awk '{print $2}' || true)
        if [ -n "$c" ] && [ "$c" -gt 0 ] 2>/dev/null; then
            echo "$c ${r:-24}"
            return
        fi
    fi

    # 6. Check environment variable COLUMNS/LINES
    if [ -n "$COLUMNS" ] && [ "$COLUMNS" -gt 0 ] 2>/dev/null; then
        echo "$COLUMNS ${LINES:-24}"
        return
    fi

    # 7. Fallback default
    echo "80 24"
}

read -r TERM_COLS TERM_LINES <<< "$(detect_terminal_geometry)"
TERM_COLS=${TERM_COLS:-80}
TERM_LINES=${TERM_LINES:-24}

# Export so Go child process inherits the detected terminal geometry
export COLUMNS="$TERM_COLS"
export LINES="$TERM_LINES"

BOX_WIDTH=48
if [ "$TERM_COLS" -gt "$BOX_WIDTH" ]; then
    PAD_LEN=$(( (TERM_COLS - BOX_WIDTH) / 2 ))
    PAD=$(printf '%*s' "$PAD_LEN" "")
else
    PAD=""
fi

echo ""
echo -e "${PAD}${CYAN}${BOLD}╔══════════════════════════════════════════════╗${NC}"
echo -e "${PAD}${CYAN}${BOLD}║           NEFARIOUS HUB LAUNCHER             ║${NC}"
echo -e "${PAD}${CYAN}${BOLD}║        Open-Source Termux Automation         ║${NC}"
echo -e "${PAD}${CYAN}${BOLD}╚══════════════════════════════════════════════╝${NC}"
echo ""

# Architecture & Bitness Detection (Dual Kernel + Userspace aware)
USER_ARCH=""
if command -v dpkg >/dev/null 2>&1; then
    USER_ARCH=$(dpkg --print-architecture 2>/dev/null || echo "")
fi

KERNEL_ARCH=$(uname -m 2>/dev/null || echo "")
LONG_BIT=$(getconf LONG_BIT 2>/dev/null || echo "")

case "$USER_ARCH" in
    aarch64|arm64)
        TARGET_BIN="nefhub_arm64"
        BIT_DESC="64-bit (aarch64)"
        ;;
    arm|armhf|armel)
        TARGET_BIN="nefhub_arm"
        BIT_DESC="32-bit (arm)"
        ;;
    x86_64|amd64)
        TARGET_BIN="nefhub_amd64"
        BIT_DESC="64-bit (x86_64)"
        ;;
    i686|i386)
        TARGET_BIN="nefhub_arm"
        BIT_DESC="32-bit (x86)"
        ;;
    *)
        if [ "$LONG_BIT" = "32" ]; then
            TARGET_BIN="nefhub_arm"
            BIT_DESC="32-bit (Userspace 32-bit)"
        elif [ "$KERNEL_ARCH" = "aarch64" ] || [ "$KERNEL_ARCH" = "arm64" ]; then
            TARGET_BIN="nefhub_arm64"
            BIT_DESC="64-bit (aarch64)"
        elif [ "$KERNEL_ARCH" = "x86_64" ] || [ "$KERNEL_ARCH" = "amd64" ]; then
            TARGET_BIN="nefhub_amd64"
            BIT_DESC="64-bit (x86_64)"
        elif [ "$KERNEL_ARCH" = "armv7l" ] || [ "$KERNEL_ARCH" = "armv8l" ] || [ "$KERNEL_ARCH" = "arm" ]; then
            TARGET_BIN="nefhub_arm"
            BIT_DESC="32-bit (armv7l)"
        else
            TARGET_BIN="nefhub_arm64"
            BIT_DESC="64-bit"
        fi
        ;;
esac

echo -e "${PAD}${GRAY}[*] Architecture : ${CYAN}$BIT_DESC${GRAY} -> ${CYAN}$TARGET_BIN${NC}"

# Ensure curl is available
if ! command -v curl >/dev/null 2>&1; then
    echo -e "${PAD}${AMBER}[!] curl not found, installing...${NC}"
    if command -v pkg >/dev/null 2>&1; then
        pkg install -y curl
    elif command -v apt-get >/dev/null 2>&1; then
        apt-get install -y curl
    fi
fi

# Fetch remote version
REMOTE_VER=$(curl -sL "$VERSION_URL" 2>/dev/null | head -n 1 | tr -d '[:space:]')
if [ -z "$REMOTE_VER" ]; then
    REMOTE_VER="latest"
fi

echo -e "${PAD}${GREEN}[✓] Latest release: v$REMOTE_VER${NC}"
echo -e "${PAD}${GRAY}[*] Downloading precompiled binary...${NC}"

# Clean up old binary to ensure fresh download
rm -f "$LOCAL_BIN"

# Download precompiled binary with cache-busting query
DOWNLOAD_URL="$BASE_URL/$TARGET_BIN?t=$(date +%s)"
curl -sL -H "Cache-Control: no-cache" "$DOWNLOAD_URL" -o "$LOCAL_BIN"

if [ ! -s "$LOCAL_BIN" ]; then
    echo -e "${PAD}${RED}[✗] Failed to download binary from $BASE_URL/$TARGET_BIN${NC}"
    exit 1
fi

chmod +x "$LOCAL_BIN"

# Android Bionic Linker Compatibility Guard
# 1. Enforce 64-byte PT_TLS segment alignment (prevents ARM64 Bionic abort)
if [ "$TARGET_BIN" = "nefhub_arm64" ] || [ "$TARGET_BIN" = "nefhub_amd64" ]; then
    printf '\x40' | dd of="$LOCAL_BIN" bs=1 seek=616 count=1 conv=notrunc >/dev/null 2>&1 || true
fi

# 2. Clean ELF headers with termux-elf-cleaner if available on device
if command -v termux-elf-cleaner >/dev/null 2>&1; then
    termux-elf-cleaner "$LOCAL_BIN" >/dev/null 2>&1 || true
fi

clear

# Execute with TTY attachment for interactive menu
if [ -e /dev/tty ]; then
    exec "$LOCAL_BIN" "$@" < /dev/tty
else
    exec "$LOCAL_BIN" "$@"
fi
