-- Prove2me | Theorems.Thm_Poly1305Debian_internalOk_poly1305_finish_of_blocks_whole
-- name    : Poly1305Debian.internalOk_poly1305_finish_of_blocks_whole
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-25T20:44:20.111905+00:00
-- url     : https://prove2.me/theorems/60c71392-d346-512b-99ea-314e04c2b803
-- title:
--   Debian libsodium Poly1305, poly1305_finish from the whole-block contract of poly1305_blocks
-- statement:
--   If the internal `poly1305_blocks` of Debian's AArch64 libsodium 1.0.22-2 object code (`libsodiumDebianOnetimeauthLib`, bundle `Poly1305Debian_Spec`) meets `blocksSpec` restricted to messages whose length is a multiple of 16 (the precondition gains $|m| \bmod 16 = 0$; the postcondition is unchanged) under `internalOk`, then the internal `poly1305_finish` meets `finishSpec` under `internalOk`.
--
--   This is a named step of the milestone `Poly1305Debian.internalOk_poly1305_finish`: `poly1305_finish` calls `poly1305_blocks` only once, with the 16-byte padded last block, so it needs no more of the block routine than this whole-block contract. The published `Poly1305Debian.internalOk_poly1305_blocks` (any length $\ge 16$) is disproved: GCC's loop in `poly1305_blocks` runs past a message whose length is not a multiple of 16. The hypothesis here is the corrected contract.
-- source:
--   Debian libsodium 1.0.22-2 (arm64), libsodium-dev_1.0.22-2_arm64.deb (https://deb.debian.org/debian/pool/main/libs/libsodium/libsodium-dev_1.0.22-2_arm64.deb), libsodium.a, poly1305_finish (poly1305_donna64.h) meets finishSpec given the whole-block contract of poly1305_blocks; a named step of the mission milestone Poly1305Debian.internalOk_poly1305_finish

import Definitions.Def_Poly1305Debian_Spec

open Arm64

namespace Poly1305Debian

theorem internalOk_poly1305_finish_of_blocks_whole :
    internalOk "poly1305_blocks [libsodium_la_poly1305_donna]"
        (fun _ => { blocksSpec with
          pre := fun g s0 =>
            match g with
            | (_, _, _, m) => ⌜m.length % 16 = 0⌝ ∗ blocksSpec.pre g s0 }) →
      internalOk "poly1305_finish [libsodium_la_poly1305_donna]" (fun _ => finishSpec) := by
  sorry

end Poly1305Debian
