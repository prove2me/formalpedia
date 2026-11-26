-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_normal_elementaryAbelian_quotient_interval_card_eq
-- name    : SharpIntermediateSubgroupBounds.manuscript_normal_elementaryAbelian_quotient_interval_card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:01:56.067829+00:00
-- url     : https://prove2.me/theorems/25e32742-a8c5-4ad0-9b56-b096afcff67f
-- title:
--   Sharp Intermediate Subgroup Bounds: manuscript normal elementary Abelian quotient interval card eq
-- statement:
--   A normal inclusion with elementary-abelian quotient has the exact same
--   closed-interval count as the standard witness.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L243-L248
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Manuscript.lean#L243-L248

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

theorem SharpIntermediateSubgroupBounds.manuscript_normal_elementaryAbelian_quotient_interval_card_eq
    {G : Type*} [Group G] [Fintype G] {p n : ℕ}
    (H : Subgroup G) [H.Normal]
    (e : (G ⧸ H) ≃* ElementaryAbelianGroup p n) [Fact p.Prime] :
    Fintype.card (Set.Ici H) = totalQBinom p n := by sorry
