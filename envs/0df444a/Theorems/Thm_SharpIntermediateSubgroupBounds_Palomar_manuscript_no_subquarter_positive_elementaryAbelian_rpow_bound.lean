-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_Palomar_manuscript_no_subquarter_positive_elementaryAbelian_rpow_bound
-- name    : SharpIntermediateSubgroupBounds.Palomar.manuscript_no_subquarter_positive_elementaryAbelian_rpow_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:04:23.112576+00:00
-- url     : https://prove2.me/theorems/2dae8cb1-19a0-4e68-92db-02faf66ea94e
-- title:
--   Palomar: manuscript no subquarter positive elementary Abelian rpow bound
-- statement:
--   Palomar-facing `Nat.card` form of optimality of the exponent `1/4`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/Solution.lean#L70-L77
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/Solution.lean#L70-L77

import Definitions.Def_SharpIntermediateSubgroupBounds
import Definitions.Def_SharpIntermediateSubgroupBounds_Solution
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_no_subquarter_positive_elementaryAbelian_rpow_bound

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open SharpIntermediateSubgroupBounds.Palomar
open scoped BigOperators Topology
open Filter Finset Real
noncomputable section

theorem SharpIntermediateSubgroupBounds.Palomar.manuscript_no_subquarter_positive_elementaryAbelian_rpow_bound
    {p : ℕ} [Fact p.Prime] {alpha C : ℝ} (halpha : alpha < 1 / 4) :
    ¬ ∀ a : ℕ, 0 < a →
      (Nat.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤
        C * Real.rpow (p : ℝ) (4 * alpha * (a : ℝ) ^ 2) := by sorry
