-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_sharpConstant_le_of_elementaryAbelian_bound
-- name    : SharpIntermediateSubgroupBounds.manuscript_sharpConstant_le_of_elementaryAbelian_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:01:55.860994+00:00
-- url     : https://prove2.me/theorems/a7ec149a-5f9b-47ab-a998-05b12a8b39f6
-- title:
--   Sharp Intermediate Subgroup Bounds: manuscript sharp Constant le of elementary Abelian bound
-- statement:
--   Any constant which bounds every normalized elementary-abelian subgroup
--   interval is at least the sharp Euler--theta constant.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L177-L185
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L177-L185

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

theorem SharpIntermediateSubgroupBounds.manuscript_sharpConstant_le_of_elementaryAbelian_bound
    {p : ℕ} [Fact p.Prime] {C : ℝ}
    (hC : ∀ a : ℕ,
      (p : ℝ)⁻¹ ^ (a * a) *
        (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤ C) :
    sharpConstant (p : ℝ) ≤ C := by sorry
