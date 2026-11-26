-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_no_subquarter_rpow_bound
-- name    : SharpIntermediateSubgroupBounds.no_subquarter_rpow_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:48:39.321836+00:00
-- url     : https://prove2.me/theorems/d170689e-dbb3-515d-a340-254a3e09c8ce
-- title:
--   Sharp Intermediate Subgroup Bounds: no subquarter rpow bound
-- statement:
--   Unnormalized `Real.rpow` form of exponent optimality.  The order of the
--   elementary-abelian group is `p^(2a)`, so an exponent `α` on the square of
--   the base-`p` logarithm gives the power `p^(4αa²)`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L1219-L1255
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean#L1219-L1255

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real

theorem SharpIntermediateSubgroupBounds.no_subquarter_rpow_bound {p : ℕ} (hp : 2 ≤ p) {α C : ℝ}
    (hα : α < 1 / 4) :
    ¬ ∀ a : ℕ,
      (totalQBinom p (2 * a) : ℝ) ≤
        C * Real.rpow (p : ℝ) (4 * α * (a : ℝ) ^ 2) := by sorry
