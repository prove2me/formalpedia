-- Prove2me | Theorems.Thm_Poly1305DebianCt_ctInternalOk_poly1305_finish
-- name    : Poly1305DebianCt.ctInternalOk_poly1305_finish
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-26T10:20:42.986284+00:00
-- url     : https://prove2.me/theorems/5af5c18d-a04a-4289-95f5-8c5f8811a611
-- title:
--   poly1305_donna64.h, poly1305_finish — constant time for a given leftover (Debian's libsodium, AArch64)
-- statement:
--   The internal function `poly1305_finish` of `libsodiumDebianOnetimeauthCtLib` (Debian's AArch64 objects of libsodium 1.0.22, unmodified; a symbol of the code block, though not exported) is constant-time in the leakage model `Leakage.ct_subroutine_ok`: `ctInternalOk "poly1305_finish [libsodium_la_poly1305_donna]" finishPre leftoverPub` (bundle `Poly1305DebianCt_Spec`), under every placement and hook table the judgment admits (`Placeable`, `GuardUniform`, `Link.PlacedLib.LinkOk`, and hooks for `sodium_memzero` and `memset` meeting `Libc.explicitBzeroSpec` and `VerifiedLibraries.Musl.cryptoMemsetSpec`; a call of `memset` reveals `x0`–`x2`, one of `sodium_memzero` `x0`–`x1`).
--
--   In detail: take two entry states at the function's address that follow the calling convention, have the code loaded and hold the same values in every register, so with the same `st` and `mac` in `x0` and `x1`. Suppose the memory of each holds, separately from an arbitrary frame of its own, `finishPre` for its own ghost value $(st, mac)$: 96 owned state bytes $st$ at `st` whose `leftover` word (offset 64) is below 16, 16 owned bytes at `mac`, and the 4128 bytes below the stack pointer. Suppose the two `leftover` words are equal. Then the two runs reveal the same sequence of observations up to their return and stop together, whatever `r`, `h`, `pad`, the buffered bytes and the `final` byte are. No limb invariant is assumed.
-- source:
--   libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda), src/libsodium/crypto_onetimeauth/poly1305/donna/poly1305_donna64.h lines 135–221 (poly1305_finish), libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda)

import Definitions.Def_Poly1305DebianCt_Spec

namespace Poly1305DebianCt

theorem ctInternalOk_poly1305_finish :
    ctInternalOk "poly1305_finish [libsodium_la_poly1305_donna]" finishPre leftoverPub := by
  sorry

end Poly1305DebianCt
