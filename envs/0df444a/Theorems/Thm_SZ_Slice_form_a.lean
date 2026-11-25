-- Prove2me | Theorems.Thm_SZ_Slice_form_a
-- name    : SZ.Slice.form_a
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:58:28.491831+00:00
-- url     : https://prove2.me/theorems/28ecd031-57a1-47e0-96a1-670dd8d76e75
-- title:
--   Slice: form a
-- statement:
--   The first form of `√m ≥ p`, the paper's (5.3): `(p-1)(√m+1) ≤ e`, expanded so that
--   `linarith` can use it.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L95-L101
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean#L95-L101

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}

theorem SZ.Slice.form_a (he : S.e = (S.m : ℤ) - 1) (hp : (S.p : ℝ) ≤ S.sq) :
    (S.p : ℝ) * S.sq + (S.p : ℝ) ≤ (S.e : ℝ) + S.sq + 1 := by sorry
