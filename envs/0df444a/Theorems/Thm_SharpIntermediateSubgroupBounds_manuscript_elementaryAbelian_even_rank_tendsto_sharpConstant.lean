-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_even_rank_tendsto_sharpConstant
-- name    : SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_even_rank_tendsto_sharpConstant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:46:21.491443+00:00
-- url     : https://prove2.me/theorems/4d60ebcb-ea1d-4a79-a5f9-c86e3613420c
-- title:
--   Sharp Intermediate Subgroup Bounds: manuscript elementary Abelian even rank tendsto sharp Constant
-- statement:
--   The normalized number of subgroups of the elementary-abelian group of
--   even rank tends to the sharp Euler--theta constant.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L121-L128
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L121-L128

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

theorem SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_even_rank_tendsto_sharpConstant
    {p : ℕ} [Fact p.Prime] :
    Tendsto (fun a : ℕ ↦
      (p : ℝ)⁻¹ ^ (a * a) *
        (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ)) atTop
      (nhds (sharpConstant (p : ℝ))) := by sorry
