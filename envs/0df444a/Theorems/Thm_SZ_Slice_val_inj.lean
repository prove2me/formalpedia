-- Prove2me | Theorems.Thm_SZ_Slice_val_inj
-- name    : SZ.Slice.val_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:44:48.586972+00:00
-- url     : https://prove2.me/theorems/7d058f2d-c325-492d-b4b5-56e205d1efb1
-- title:
--   Slice: val inj
-- statement:
--   `ℤ[√m]` is free on `1, √m`: the coordinates of a state are well defined.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L151-L161
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L151-L161

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)

theorem SZ.Slice.val_inj {p q p' q' : ℤ}
    (h : (p : ℝ) + (q : ℝ) * S.sq = (p' : ℝ) + (q' : ℝ) * S.sq) : p = p' ∧ q = q' := by sorry
