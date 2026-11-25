-- Prove2me | Theorems.Thm_SZ_Slice_stt_snd_lower
-- name    : SZ.Slice.stt_snd_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:01:08.563335+00:00
-- url     : https://prove2.me/theorems/68a4d326-4d9f-4ce9-b0b7-b8e51bad1037
-- title:
--   Slice: stt snd lower
-- statement:
--   **Growth.**  The `√m`-coordinate of the state satisfies `Q k ≥ p m^{k+1} + m`; in
--   particular it always exceeds `m`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L143-L170
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L143-L170

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}

theorem SZ.Slice.stt_snd_lower (he : S.e = (S.m : ℤ) - 1) {j k₀ : ℤ} (hk : 1 ≤ k₀)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) (k : ℕ) :
    S.p * (S.m : ℤ) ^ (k + 1) + (S.m : ℤ) ≤ (stt S j k₀ k).2 := by sorry
