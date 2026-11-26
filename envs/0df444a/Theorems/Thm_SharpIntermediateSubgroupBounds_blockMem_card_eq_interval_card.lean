-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_blockMem_card_eq_interval_card
-- name    : SharpIntermediateSubgroupBounds.blockMem_card_eq_interval_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:03.339897+00:00
-- url     : https://prove2.me/theorems/344f19df-9d85-5da6-a87a-89a6f3140a3d
-- title:
--   Sharp Intermediate Subgroup Bounds: block Mem card eq interval card
-- statement:
--   In a finite transitive action, the blocks containing `a` are equinumerous
--   with the subgroups containing the stabilizer of `a`.
--
--   This is the exact cardinal form of the block--subgroup correspondence used to
--   transfer subgroup-interval estimates to transitive permutation actions.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Blocks.lean#L109-L113
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Blocks.lean#L109-L113

import Mathlib.GroupTheory.GroupAction.Blocks
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Blocks
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open MulAction
open scoped Pointwise
variable (G X : Type*) [Group G] [Fintype G] [Fintype X]
variable [MulAction G X] [MulAction.IsPretransitive G X]
attribute [local instance] SharpIntermediateSubgroupBounds.blockMemFintype
attribute [local instance] SharpIntermediateSubgroupBounds.blocksSubgroupFinite
attribute [local instance] SharpIntermediateSubgroupBounds.blocksIntervalFintype
attribute [local instance] SharpIntermediateSubgroupBounds.systemOfImprimitivityFintype

theorem SharpIntermediateSubgroupBounds.blockMem_card_eq_interval_card (a : X) :
    Fintype.card (MulAction.BlockMem G a) =
      Fintype.card (Set.Ici (MulAction.stabilizer G a)) := by sorry
