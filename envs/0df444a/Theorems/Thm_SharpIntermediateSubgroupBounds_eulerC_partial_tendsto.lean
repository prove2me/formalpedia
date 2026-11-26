-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_eulerC_partial_tendsto
-- name    : SharpIntermediateSubgroupBounds.eulerC_partial_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:41:01.396113+00:00
-- url     : https://prove2.me/theorems/98142f0c-275d-5ee0-a35f-5b5c58381591
-- title:
--   Sharp Intermediate Subgroup Bounds: euler C partial tendsto
-- statement:
--   The finite inverse Euler products converge to `eulerC`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Theta.lean#L117-L120
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Theta.lean#L117-L120

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

theorem SharpIntermediateSubgroupBounds.eulerC_partial_tendsto {p : ℝ} (hp : 2 ≤ p) :
    Tendsto (fun r : ℕ ↦ ∏ n ∈ Finset.range r, (1 - p⁻¹ ^ (n + 1))⁻¹)
      atTop (nhds (eulerC p)) := by sorry
