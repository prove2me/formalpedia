-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_fixed_layer_eq
-- name    : SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_fixed_layer_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:01:52.307847+00:00
-- url     : https://prove2.me/theorems/684c2a43-f75f-44eb-a3ba-03ecb4aefd78
-- title:
--   Sharp Intermediate Subgroup Bounds: manuscript elementary Abelian fixed layer eq
-- statement:
--   Every fixed index layer of the elementary-abelian witness attains the
--   Gaussian-binomial layer bound.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L235-L239
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L235-L239

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

theorem SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_fixed_layer_eq (p n k : ℕ)
    [Fact p.Prime] (hk : k ≤ n) :
    (primePowerLayer p k
      (⊥ : Subgroup (ElementaryAbelianGroup p n)) ⊤).card = qBinom p n k := by sorry
