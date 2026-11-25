-- Prove2me | Theorems.Thm_Poly1305Debian_internalOk_poly1305_update_of_blocks_whole
-- name    : Poly1305Debian.internalOk_poly1305_update_of_blocks_whole
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-25T20:53:14.127811+00:00
-- url     : https://prove2.me/theorems/479c0592-0282-532f-98ec-b193a4abff70
-- title:
--   Debian libsodium Poly1305, poly1305_update from the whole-block contract of poly1305_blocks
-- statement:
--   If the internal `poly1305_blocks` of Debian's AArch64 libsodium 1.0.22-2 object code (`libsodiumDebianOnetimeauthLib`, bundle `Poly1305Debian_Spec`) meets `blocksSpec` restricted to messages whose length is a multiple of 16 (the precondition gains $|m| \bmod 16 = 0$; the postcondition is unchanged) under `internalOk`, then the internal `poly1305_update` meets `updateIntSpec` under `internalOk`.
--
--   This is a named step of the milestone `Poly1305Debian.internalOk_poly1305_update`: `poly1305_update` calls `poly1305_blocks` only on the full 16-byte buffer and on the largest multiple of 16 bytes of the rest of the message, so it needs no more of the block routine than this whole-block contract. The published `Poly1305Debian.internalOk_poly1305_blocks` (any length $\ge 16$) is disproved: GCC's loop in `poly1305_blocks` runs past a message whose length is not a multiple of 16. The hypothesis here is the corrected contract.
-- source:
--   Debian libsodium 1.0.22-2 (arm64), libsodium-dev_1.0.22-2_arm64.deb (https://deb.debian.org/debian/pool/main/libs/libsodium/libsodium-dev_1.0.22-2_arm64.deb), libsodium.a, poly1305_update (poly1305_donna.c) meets updateIntSpec given the whole-block contract of poly1305_blocks; a named step of the mission milestone Poly1305Debian.internalOk_poly1305_update

import Definitions.Def_Poly1305Debian_Spec

open Arm64

namespace Poly1305Debian

theorem internalOk_poly1305_update_of_blocks_whole :
    internalOk "poly1305_blocks [libsodium_la_poly1305_donna]"
        (fun _ => { blocksSpec with
          pre := fun g s0 =>
            match g with
            | (_, _, _, m) => ⌜m.length % 16 = 0⌝ ∗ blocksSpec.pre g s0 }) →
      internalOk "poly1305_update [libsodium_la_poly1305_donna]" (fun _ => updateIntSpec) := by
  sorry

end Poly1305Debian
