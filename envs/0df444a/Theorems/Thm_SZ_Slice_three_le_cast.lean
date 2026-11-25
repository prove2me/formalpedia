-- Prove2me | Theorems.Thm_SZ_Slice_three_le_cast
-- name    : SZ.Slice.three_le_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:43:20.966851+00:00
-- url     : https://prove2.me/theorems/9db83844-4acc-49b7-a95c-b5fff1904a41
-- title:
--   Slice: three le cast
-- statement:
--   The Slice construction uses the three le cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L163-L163
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L163-L163

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

theorem SZ.Slice.three_le_cast : (3 : ℝ) ≤ (S.m : ℝ) := by sorry
