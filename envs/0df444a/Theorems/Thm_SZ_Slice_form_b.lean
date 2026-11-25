-- Prove2me | Theorems.Thm_SZ_Slice_form_b
-- name    : SZ.Slice.form_b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:59:05.817748+00:00
-- url     : https://prove2.me/theorems/7101b6fe-affc-4747-9cb5-a7ef5200f13d
-- title:
--   Slice: form b
-- statement:
--   The second form of `√m ≥ p`, the paper's (5.3): `m(U - p) ≥ p√m`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L104-L111
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L104-L111

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}

theorem SZ.Slice.form_b (he : S.e = (S.m : ℤ) - 1) (hp : (S.p : ℝ) ≤ S.sq) :
    (S.p : ℝ) * S.sq ≤ (S.m : ℝ) * (S.U - (S.p : ℝ)) := by sorry
