-- Prove2me | Theorems.Thm_Poly1305Debian_internalOk_donna_oneshot
-- name    : Poly1305Debian.internalOk_donna_oneshot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-25T21:19:50.55486+00:00
-- url     : https://prove2.me/theorems/23dd9837-2a8e-41f6-b7af-3d4b95d947cc
-- title:
--   poly1305_donna.c — the donna one-shot computes RFC 8439's Poly1305 tag (Debian AArch64 object code)
-- statement:
--   `donnaOneshotOk` (bundle `Poly1305Debian_Spec`): the static function `crypto_onetimeauth_poly1305_donna` of Debian's libsodium 1.0.22-2 arm64 object code (`libsodiumDebianOnetimeauthLib`) meets `oneshotSpec`, under every placement of the library that is `Placeable` and `GuardUniform` and every hook table with `MemzeroOk`, `MemsetOk` and `Link.PlacedLib.LinkOk` (`internalOk`).
--
--   In detail: take any entry state at the function with the stack pointer 16-byte aligned, and any frame $R$ held separately. Suppose `x0 = out` points to 16 owned bytes, `x1 = m` to the message bytes $m$ (owned or read-only), `x2` $= |m|$, `x3 = key` to the 32 key bytes $key$ (owned or read-only), the stack-protector guard is readable where the code reads it (`guardRes`), and the 4320 bytes below the stack pointer are owned. Then execution terminates and returns to the link register. The stack pointer and the callee-saved registers are restored, $R$ is untouched, and `w0` is `0`. The 16 bytes at `out` are `poly1305Mac m key` (RFC 8439 §2.5.1). $m$, $key$, the guard and the stack bytes are handed back. The run never panics, exits or runs out of memory.
--
--   This is the second conjunct of the milestone `Poly1305Debian.internalOk_donna_init_update_final_oneshot` of the mission on this object code, stated on its own so that its proof can be checked separately.
-- source:
--   Debian libsodium 1.0.22-2 (arm64), libsodium-dev_1.0.22-2_arm64.deb (https://deb.debian.org/debian/pool/main/libs/libsodium/libsodium-dev_1.0.22-2_arm64.deb), libsodium.a, poly1305_donna.c, crypto_onetimeauth_poly1305_donna (lines 58-70): the one-shot conjunct of milestone Poly1305Debian.internalOk_donna_init_update_final_oneshot

import Definitions.Def_Poly1305Debian_Spec

namespace Poly1305Debian

theorem internalOk_donna_oneshot : donnaOneshotOk := by
  sorry

end Poly1305Debian
