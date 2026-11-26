-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_layer_card_moment
-- name    : SharpIntermediateSubgroupBounds.layer_card_moment
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:44:16.139932+00:00
-- url     : https://prove2.me/theorems/0acc8433-4548-4680-8552-3f3ef184bd9a
-- title:
--   Sharp Intermediate Subgroup Bounds: layer card moment
-- statement:
--   Rational layer bound retaining the exact index `m`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L411-L452
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L411-L452

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

theorem SharpIntermediateSubgroupBounds.layer_card_moment {H : Subgroup G} (hn : 1 < H.index)
    {q r m : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac)
    (hmi : m < q ^ (r + 1)) :
    gammaQ q r * (Nat.card (layer H m) : ℚ) * (m : ℚ) ^ r ≤
      (H.index : ℚ) ^ r := by sorry
