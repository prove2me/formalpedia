-- Prove2me | Theorems.Thm_Poly1305DebianCt_ctInternalOk_poly1305_blocks
-- name    : Poly1305DebianCt.ctInternalOk_poly1305_blocks
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-26T10:20:05.318261+00:00
-- url     : https://prove2.me/theorems/6097e364-f283-409d-92fd-3498e10e88b7
-- title:
--   poly1305_donna64.h, poly1305_blocks — constant time in r, h and the message (Debian's libsodium, AArch64)
-- statement:
--   The internal function `poly1305_blocks` of `libsodiumDebianOnetimeauthCtLib` (Debian's AArch64 objects of libsodium 1.0.22, unmodified; a symbol of the code block, though not exported) is constant-time in the leakage model `Leakage.ct_subroutine_ok`: `ctInternalOk "poly1305_blocks [libsodium_la_poly1305_donna]" blocksPre blocksPub` (bundle `Poly1305DebianCt_Spec`), under every placement and hook table the judgment admits (`Placeable`, `GuardUniform`, `Link.PlacedLib.LinkOk`, and hooks for `sodium_memzero` and `memset` meeting `Libc.explicitBzeroSpec` and `VerifiedLibraries.Musl.cryptoMemsetSpec`).
--
--   In detail: take two entry states at the function's address that follow the calling convention, have the code loaded and hold the same values in every register, so with the same `st`, `m` and `bytes` in `x0`–`x2`. Suppose the memory of each holds, separately from an arbitrary frame of its own, `blocksPre` for its own ghost value $(ro, rh, fin, m)$: 48 owned bytes $rh$ (`r` and `h`) at `st`, the owned `final` byte $fin$ at `st + 88`, and the message bytes $m$ at `m` (owned or read-only, by $ro$), with `bytes` $= |m|$ a nonzero multiple of 16. Suppose the two ghost values agree on $ro$ and $fin$. Then the two runs reveal the same sequence of observations up to their return and stop together, whatever `r`, `h` and the message bytes are. No stack is used, and no limb invariant is assumed.
-- source:
--   libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda), src/libsodium/crypto_onetimeauth/poly1305/donna/poly1305_donna64.h lines 61–133 (poly1305_blocks), libsodium 1.0.22-RELEASE, commit 77e1ce5d6dee871c49ef211222ba18ef0c486bda (https://github.com/jedisct1/libsodium/tree/77e1ce5d6dee871c49ef211222ba18ef0c486bda)

import Definitions.Def_Poly1305DebianCt_Spec

namespace Poly1305DebianCt

theorem ctInternalOk_poly1305_blocks :
    ctInternalOk "poly1305_blocks [libsodium_la_poly1305_donna]" blocksPre blocksPub := by
  sorry

end Poly1305DebianCt
