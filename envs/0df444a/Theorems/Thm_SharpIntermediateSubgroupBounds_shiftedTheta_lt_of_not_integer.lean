-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_shiftedTheta_lt_of_not_integer
-- name    : SharpIntermediateSubgroupBounds.shiftedTheta_lt_of_not_integer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:42:05.169144+00:00
-- url     : https://prove2.me/theorems/402583de-1a55-5a8f-8f5f-e34efe3f1c75
-- title:
--   Sharp Intermediate Subgroup Bounds: shifted Theta lt of not integer
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the shifted Theta lt of not integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Theta.lean#L363-L395
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Theta.lean#L363-L395

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.shiftedTheta_lt_of_not_integer {p x : ℝ} (hp : 1 < p)
    (hx : ¬ ∃ z : ℤ, (z : ℝ) = x) :
    shiftedTheta p x < gaussianTheta p := by sorry
