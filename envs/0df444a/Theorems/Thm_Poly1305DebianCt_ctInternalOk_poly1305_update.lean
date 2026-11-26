-- Prove2me | Theorems.Thm_Poly1305DebianCt_ctInternalOk_poly1305_update
-- name    : Poly1305DebianCt.ctInternalOk_poly1305_update
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-26T10:21:22.80522+00:00
-- url     : https://prove2.me/theorems/6b619ddc-c1d8-5797-8be2-9b8528f8a47c
-- title:
--   poly1305_donna.c, poly1305_update — constant time for a given leftover and length (Debian's libsodium, AArch64)
-- statement:
--   The internal function `poly1305_update` of `libsodiumDebianOnetimeauthCtLib` (Debian's AArch64 objects of libsodium 1.0.22, unmodified; a symbol of the code block, though not exported) is constant-time in the leakage model `Leakage.ct_subroutine_ok`: `ctInternalOk "poly1305_update [libsodium_la_poly1305_donna]" updateIntPre updatePub` (bundle `Poly1305DebianCt_Spec`), under every placement and hook table the judgment admits (`Placeable`, `GuardUniform`, `Link.PlacedLib.LinkOk`, and hooks for `sodium_memzero` and `memset` meeting `Libc.explicitBzeroSpec` and `VerifiedLibraries.Musl.cryptoMemsetSpec`).
--
--   In detail: take two entry states at the function's address that follow the calling convention, have the code loaded and hold the same values in every register, so with the same `st`, `m` and `bytes` in `x0`–`x2`. Suppose the memory of each holds, separately from an arbitrary frame of its own, `updateIntPre` for its own ghost value $(ro, st, m)$: 96 owned state bytes $st$ at `st` whose `leftover` word (offset 64) is below 16, the message bytes $m$ at `m` (owned or read-only, by $ro$) with `bytes` $= |m|$, and the 32 bytes below the stack pointer. Suppose the two ghost values agree on $ro$ and on the `leftover` word. Then the two runs reveal the same sequence of observations up to their return and stop together, whatever the other state bytes and the message bytes are. No limb invariant is assumed.
-- source:
--   libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda), src/libsodium/crypto_onetimeauth/poly1305/donna/poly1305_donna.c lines 14–56 (poly1305_update), libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda)

import Definitions.Def_Poly1305DebianCt_Spec

namespace Poly1305DebianCt

theorem ctInternalOk_poly1305_update :
    ctInternalOk "poly1305_update [libsodium_la_poly1305_donna]" updateIntPre updatePub := by
  sorry

end Poly1305DebianCt
