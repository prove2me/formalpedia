-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_gaussianTheta_summable
-- name    : SharpIntermediateSubgroupBounds.gaussianTheta_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:41:04.018165+00:00
-- url     : https://prove2.me/theorems/3d15ebc1-a2d2-5d0a-b0a5-3ef9d0839da7
-- title:
--   Sharp Intermediate Subgroup Bounds: gaussian Theta summable
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the gaussian Theta summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Theta.lean#L175-L177
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Theta.lean#L175-L177

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

theorem SharpIntermediateSubgroupBounds.gaussianTheta_summable {p : ℝ} (hp : 1 < p) :
    Summable (fun z : ℤ ↦ Real.exp (-Real.log p * (z : ℝ) ^ 2)) := by sorry
