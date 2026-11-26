-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_Palomar_manuscript_sharpConstant_le_of_positive_elementaryAbelian_bound
-- name    : SharpIntermediateSubgroupBounds.Palomar.manuscript_sharpConstant_le_of_positive_elementaryAbelian_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:02:45.143825+00:00
-- url     : https://prove2.me/theorems/3182d3a5-b8b6-47d9-b27f-231951cc3a6b
-- title:
--   Palomar: manuscript sharp Constant le of positive elementary Abelian bound
-- statement:
--   Palomar-facing `Nat.card` form of optimality of the leading constant.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/Solution.lean#L58-L67
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/Solution.lean#L58-L67

import Definitions.Def_SharpIntermediateSubgroupBounds
import Definitions.Def_SharpIntermediateSubgroupBounds_Solution
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_sharpConstant_le_of_positive_elementaryAbelian_bound

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open SharpIntermediateSubgroupBounds.Palomar
open scoped BigOperators Topology
open Filter Finset Real
noncomputable section

theorem SharpIntermediateSubgroupBounds.Palomar.manuscript_sharpConstant_le_of_positive_elementaryAbelian_bound
    {p : ℕ} [Fact p.Prime] {C : ℝ}
    (hC : ∀ a : ℕ, 0 < a →
      (p : ℝ)⁻¹ ^ (a * a) *
        (Nat.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤ C) :
    sharpConstant (p : ℝ) ≤ C := by sorry
