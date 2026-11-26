-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_bottom_index
-- name    : SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_bottom_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:46:23.325219+00:00
-- url     : https://prove2.me/theorems/51a0b134-4890-4661-9d19-9511ce87796c
-- title:
--   Sharp Intermediate Subgroup Bounds: manuscript elementary Abelian bottom index
-- statement:
--   The index of the trivial subgroup in the even-rank elementary-abelian
--   witness is exactly `p^(2a)`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L43-L47
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L43-L47

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

theorem SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_bottom_index (p a : ℕ)
    [Fact p.Prime] :
    (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index = p ^ (2 * a) := by sorry
