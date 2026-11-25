-- Prove2me | Theorems.Thm_SZ_Slice_sq_sq
-- name    : SZ.Slice.sq_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:16:55.788015+00:00
-- url     : https://prove2.me/theorems/22020ce7-280c-4785-a04d-e78b1b86fecc
-- title:
--   Slice: sq sq
-- statement:
--   The Slice construction uses the sq sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L136-L137
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L136-L137

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

theorem SZ.Slice.sq_sq : S.sq ^ 2 = (S.m : ℝ) := by sorry
