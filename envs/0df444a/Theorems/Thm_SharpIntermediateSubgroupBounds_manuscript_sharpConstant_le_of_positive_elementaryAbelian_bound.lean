-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_sharpConstant_le_of_positive_elementaryAbelian_bound
-- name    : SharpIntermediateSubgroupBounds.manuscript_sharpConstant_le_of_positive_elementaryAbelian_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:46:32.348066+00:00
-- url     : https://prove2.me/theorems/7c10a187-5db4-4493-ab34-aabeac521d01
-- title:
--   Sharp Intermediate Subgroup Bounds: manuscript sharp Constant le of positive elementary Abelian bound
-- statement:
--   Manuscript-domain form of constant optimality.  Only positive ranks are
--   assumed, exactly matching the `index > 1` domain of the sharp interval bound.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L189-L197
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L189-L197

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open Filter
noncomputable section
attribute [local instance] SharpIntermediateSubgroupBounds.manuscriptSubgroupIntervalFintype

theorem SharpIntermediateSubgroupBounds.manuscript_sharpConstant_le_of_positive_elementaryAbelian_bound
    {p : ℕ} [Fact p.Prime] {C : ℝ}
    (hC : ∀ a : ℕ, 0 < a →
      (p : ℝ)⁻¹ ^ (a * a) *
        (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤ C) :
    sharpConstant (p : ℝ) ≤ C := by sorry
