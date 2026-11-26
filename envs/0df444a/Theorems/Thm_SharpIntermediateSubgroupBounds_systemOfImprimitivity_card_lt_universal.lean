-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_systemOfImprimitivity_card_lt_universal
-- name    : SharpIntermediateSubgroupBounds.systemOfImprimitivity_card_lt_universal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:32.532021+00:00
-- url     : https://prove2.me/theorems/63fe5ee0-e7a7-439b-b07b-d2dfbb63d9dc
-- title:
--   Sharp Intermediate Subgroup Bounds: system Of Imprimitivity card lt universal
-- statement:
--   The sharp universal bound for the number of genuine invariant systems
--   of imprimitivity of a finite transitive action.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Blocks.lean#L147-L154
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Blocks.lean#L147-L154

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

theorem SharpIntermediateSubgroupBounds.systemOfImprimitivity_card_lt_universal (a : X)
    (hX : 1 < Nat.card X) :
    (Fintype.card (SystemOfImprimitivity G X) : ℝ) <
      sharpConstant 2 *
        (Nat.card X : ℝ) ^ (indexLog 2 (Nat.card X) / 4) := by sorry
