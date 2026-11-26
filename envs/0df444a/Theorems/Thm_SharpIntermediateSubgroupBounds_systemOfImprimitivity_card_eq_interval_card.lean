-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_systemOfImprimitivity_card_eq_interval_card
-- name    : SharpIntermediateSubgroupBounds.systemOfImprimitivity_card_eq_interval_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:16.72078+00:00
-- url     : https://prove2.me/theorems/e446511e-a0d4-4091-a8f3-65c436b9cffa
-- title:
--   Sharp Intermediate Subgroup Bounds: system Of Imprimitivity card eq interval card
-- statement:
--   Systems of imprimitivity, rather than merely individual pointed blocks,
--   are counted exactly by the intermediate subgroups above a point stabilizer.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Blocks.lean#L117-L123
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Blocks.lean#L117-L123

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

theorem SharpIntermediateSubgroupBounds.systemOfImprimitivity_card_eq_interval_card (a : X) :
    Fintype.card (SystemOfImprimitivity G X) =
      Fintype.card (Set.Ici (MulAction.stabilizer G a)) := by sorry
