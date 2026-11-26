-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_bottom_index_minFac
-- name    : SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_bottom_index_minFac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:01:52.353412+00:00
-- url     : https://prove2.me/theorems/5903bb32-85d8-4e89-b8c7-6af99c37ba97
-- title:
--   Sharp Intermediate Subgroup Bounds: manuscript elementary Abelian bottom index min Fac
-- statement:
--   In every positive even rank, the least prime divisor of the witness
--   index is the prescribed prime `p`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L51-L55
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L51-L55

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

theorem SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_bottom_index_minFac (p a : ℕ)
    [Fact p.Prime] (ha : 0 < a) :
    (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index.minFac = p := by sorry
