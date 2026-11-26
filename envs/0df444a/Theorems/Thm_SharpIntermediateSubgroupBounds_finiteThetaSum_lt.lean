-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_finiteThetaSum_lt
-- name    : SharpIntermediateSubgroupBounds.finiteThetaSum_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:46:52.113631+00:00
-- url     : https://prove2.me/theorems/f6141459-d6aa-43e6-b0a4-f7575d479171
-- title:
--   Sharp Intermediate Subgroup Bounds: finite Theta Sum lt
-- statement:
--   Strict analytic upper bound for the finite sum.  The strictness comes from
--   the omitted tail of the reciprocal Euler product, so it remains strict even
--   when the shifted theta series itself is at a maximizing integral translate.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Theta.lean#L435-L488
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Theta.lean#L435-L488

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

theorem SharpIntermediateSubgroupBounds.finiteThetaSum_lt {p L : ℝ} (hp : 2 ≤ p) (hL : 0 ≤ L) :
    finiteThetaSum p L <
      sharpConstant p * Real.exp (Real.log p * L ^ 2 / 4) := by sorry
