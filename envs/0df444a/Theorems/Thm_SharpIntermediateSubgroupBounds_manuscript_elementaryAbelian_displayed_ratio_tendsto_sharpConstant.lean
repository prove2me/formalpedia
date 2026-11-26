-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_displayed_ratio_tendsto_sharpConstant
-- name    : SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_displayed_ratio_tendsto_sharpConstant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:46:11.311971+00:00
-- url     : https://prove2.me/theorems/fb070c70-c772-574a-9f59-cffdf4540865
-- title:
--   Sharp Intermediate Subgroup Bounds: manuscript elementary Abelian displayed ratio tendsto sharp Constant
-- statement:
--   Literal displayed ratio: the interval count divided by the
--   index-logarithmic scale tends to the sharp constant.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L132-L146
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L132-L146

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

theorem SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_displayed_ratio_tendsto_sharpConstant
    {p : ℕ} [Fact p.Prime] :
    Tendsto (fun a : ℕ ↦
      (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) /
        (((⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index : ℝ) ^
          (indexLog p
            (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index / 4)))
      atTop (nhds (sharpConstant (p : ℝ))) := by sorry
