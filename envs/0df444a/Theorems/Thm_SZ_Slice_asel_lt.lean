-- Prove2me | Theorems.Thm_SZ_Slice_asel_lt
-- name    : SZ.Slice.asel_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:07:01.327097+00:00
-- url     : https://prove2.me/theorems/0b317795-ca59-4910-b620-9fd8af1d3dd1
-- title:
--   Slice: asel lt
-- statement:
--   Above the window the rule takes the least admissible `a`: `a < v - U + p`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L297-L315
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L297-L315

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

theorem SZ.Slice.asel_lt {w : ℝ} (h : S.U < w - (S.bsel w : ℝ) * S.sq) :
    (S.asel w : ℝ) < w - (S.bsel w : ℝ) * S.sq - S.U + (S.p : ℝ) := by sorry
