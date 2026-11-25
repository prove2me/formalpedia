-- Prove2me | Theorems.Thm_Poly1305Debian_internalOk_donna_init_update_final
-- name    : Poly1305Debian.internalOk_donna_init_update_final
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-25T21:19:33.137182+00:00
-- url     : https://prove2.me/theorems/480fe439-58c8-5187-8043-a629e74b1c38
-- title:
--   poly1305_donna.c — the donna init/update/final compute RFC 8439's Poly1305 tag (Debian AArch64 object code)
-- statement:
--   There is a representation predicate $\mathrm{Rep}$ (a `Poly1305Libsodium.StateRep`: a relation between a state address, its 256 bytes, a key and a message) such that `donnaInitOk Rep`, `donnaUpdateOk Rep` and `donnaFinalOk Rep` hold (bundle `Poly1305Debian_Spec`). That is, the static functions `crypto_onetimeauth_poly1305_donna_init`, `_update` and `_final` of Debian's libsodium 1.0.22-2 arm64 object code (`libsodiumDebianOnetimeauthLib`) meet `initSpec Rep`, `updateSpec Rep` and `finalSpec Rep`. Each holds under every placement of the library that is `Placeable` and `GuardUniform` and every hook table with `MemzeroOk`, `MemsetOk` and `Link.PlacedLib.LinkOk` (`internalOk`).
--
--   In every case execution terminates and returns to the link register, with the stack pointer and the callee-saved registers restored, any separately held frame untouched, and `0` in `w0`. It never panics, exits or runs out of memory.
--   - **init** (`x0 = state`, `x1 = key`): with 256 owned bytes at `state` and the 32 key bytes $key$ (owned or read-only), it leaves 256 bytes $st'$ with $\mathrm{Rep}(\mathtt{state}, st', key, [\,])$ and hands the key back. It uses no stack.
--   - **update** (`x0 = state`, `x1 = in`, `x2 = inlen`): with 256 owned bytes $st$ such that $\mathrm{Rep}(\mathtt{state}, st, key, m)$, the bytes $inp$ (owned or read-only) and `inlen` $= |inp|$, it leaves 256 bytes $st'$ with $\mathrm{Rep}(\mathtt{state}, st', key, m \mathbin{+\!\!+} inp)$ and hands $inp$ back. It uses the 48 bytes below the stack pointer.
--   - **final** (`x0 = state`, `x1 = out`): with 256 owned bytes $st$ such that $\mathrm{Rep}(\mathtt{state}, st, key, m)$ and 16 owned bytes at `out`, it writes `poly1305Mac m key` (RFC 8439 §2.5.1) to `out`, sets the first 96 bytes of the state to zero and leaves the other 160 unchanged. It uses the 4144 bytes below the stack pointer.
--
--   This is the first conjunct of the milestone `Poly1305Debian.internalOk_donna_init_update_final_oneshot` of the mission on this object code, stated on its own so that its proof can be checked separately.
-- source:
--   Debian libsodium 1.0.22-2 (arm64), libsodium-dev_1.0.22-2_arm64.deb (https://deb.debian.org/debian/pool/main/libs/libsodium/libsodium-dev_1.0.22-2_arm64.deb), libsodium.a, poly1305_donna.c, crypto_onetimeauth_poly1305_donna_init/_update/_final (lines 72-98): the streaming conjunct of milestone Poly1305Debian.internalOk_donna_init_update_final_oneshot

import Definitions.Def_Poly1305Debian_Spec

namespace Poly1305Debian

theorem internalOk_donna_init_update_final :
    ∃ Rep : Poly1305Libsodium.StateRep, donnaInitOk Rep ∧ donnaUpdateOk Rep ∧ donnaFinalOk Rep := by
  sorry

end Poly1305Debian
