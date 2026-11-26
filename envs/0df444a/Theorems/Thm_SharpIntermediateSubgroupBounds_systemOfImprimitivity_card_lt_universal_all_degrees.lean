-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_systemOfImprimitivity_card_lt_universal_all_degrees
-- name    : SharpIntermediateSubgroupBounds.systemOfImprimitivity_card_lt_universal_all_degrees
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:02:27.380032+00:00
-- url     : https://prove2.me/theorems/3d84f2c2-9d44-57a2-80a6-6763e0567516
-- title:
--   Sharp Intermediate Subgroup Bounds: system Of Imprimitivity card lt universal all degrees
-- statement:
--   All-degree form of the system-of-imprimitivity estimate.  In degree one
--   there is exactly one invariant system and the same strict analytic bound is
--   still valid.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Blocks.lean#L159-L182
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Blocks.lean#L159-L182

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

theorem SharpIntermediateSubgroupBounds.systemOfImprimitivity_card_lt_universal_all_degrees (a : X) :
    (Fintype.card (SystemOfImprimitivity G X) : ℝ) <
      sharpConstant 2 *
        (Nat.card X : ℝ) ^ (indexLog 2 (Nat.card X) / 4) := by sorry
