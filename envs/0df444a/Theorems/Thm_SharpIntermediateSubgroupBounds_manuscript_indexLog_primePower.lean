-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_indexLog_primePower
-- name    : SharpIntermediateSubgroupBounds.manuscript_indexLog_primePower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:50:41.793815+00:00
-- url     : https://prove2.me/theorems/1790ecb9-6b9f-51ce-8303-cab3232c8b6c
-- title:
--   Sharp Intermediate Subgroup Bounds: manuscript index Log prime Power
-- statement:
--   The logarithm base `p` of the exact prime power `p^n` is `n`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L83-L88
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L83-L88

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

theorem SharpIntermediateSubgroupBounds.manuscript_indexLog_primePower (p n : ℕ) (hp : 1 < p) :
    indexLog p (p ^ n) = n := by sorry
