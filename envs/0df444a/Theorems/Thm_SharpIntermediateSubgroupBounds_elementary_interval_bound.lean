-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_elementary_interval_bound
-- name    : SharpIntermediateSubgroupBounds.elementary_interval_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:44:15.86223+00:00
-- url     : https://prove2.me/theorems/59946bb9-180f-4825-9461-8db468ab74ea
-- title:
--   Sharp Intermediate Subgroup Bounds: elementary interval bound
-- statement:
--   The elementary generating-set estimate from the introduction.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L581-L605
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L581-L605

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.packingSubgroupDecidableEq
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupFinite

theorem SharpIntermediateSubgroupBounds.elementary_interval_bound {H : Subgroup G} (hn : 1 < H.index) :
    Nat.card (interval H) ≤ H.index ^ Nat.log 2 H.index := by sorry
