-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_no_subquarter_normalized_exponential_bound
-- name    : SharpIntermediateSubgroupBounds.no_subquarter_normalized_exponential_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:36.795742+00:00
-- url     : https://prove2.me/theorems/3d7f0a44-2a64-5f6a-9976-8bfb4fc9999a
-- title:
--   Sharp Intermediate Subgroup Bounds: no subquarter normalized exponential bound
-- statement:
--   Explicit optimality of the exponent `1/4`, in normalized exponential
--   form.  For every `α < 1/4` and every fixed constant `C`, the proposed
--   normalized right side tends to zero and therefore cannot dominate all
--   elementary-abelian examples.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L1190-L1214
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L1190-L1214

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.no_subquarter_normalized_exponential_bound {p : ℕ} (hp : 2 ≤ p)
    {α C : ℝ} (hα : α < 1 / 4) :
    ¬ ∀ a : ℕ,
      (p : ℝ)⁻¹ ^ (a * a) * (totalQBinom p (2 * a) : ℝ) ≤
        C * Real.exp
          (Real.log (p : ℝ) * (4 * α - 1) * (a : ℝ) ^ 2) := by sorry
