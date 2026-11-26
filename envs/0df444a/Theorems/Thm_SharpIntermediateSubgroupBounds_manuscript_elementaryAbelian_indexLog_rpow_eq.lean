-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_indexLog_rpow_eq
-- name    : SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_indexLog_rpow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:50:38.37935+00:00
-- url     : https://prove2.me/theorems/8d2a1ef4-ebc2-498a-a90c-68beebff165f
-- title:
--   Sharp Intermediate Subgroup Bounds: manuscript elementary Abelian index Log rpow eq
-- statement:
--   The manuscript's index-logarithmic scale specializes to the centered
--   power `p^(a²)` on the even-rank elementary-abelian family.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L59-L80
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L59-L80

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

theorem SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_indexLog_rpow_eq (p a : ℕ)
    [Fact p.Prime] :
    (((⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index : ℝ) ^
        (indexLog p
          (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index / 4)) =
      (p : ℝ) ^ (a * a) := by sorry
