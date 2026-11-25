-- Prove2me | Theorems.Thm_SZ_Slice_asel_eq_zero
-- name    : SZ.Slice.asel_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:07:15.861215+00:00
-- url     : https://prove2.me/theorems/532dd65a-d0de-4081-ab6b-4afcc4a2011e
-- title:
--   Slice: asel eq zero
-- statement:
--   Below the window the rule takes `a = 0`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L289-L294
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L289-L294

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

theorem SZ.Slice.asel_eq_zero {w : ℝ} (h : w - (S.bsel w : ℝ) * S.sq ≤ S.U) : S.asel w = 0 := by sorry
