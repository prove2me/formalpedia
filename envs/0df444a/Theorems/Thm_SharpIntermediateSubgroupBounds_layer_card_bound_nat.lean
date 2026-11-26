-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_layer_card_bound_nat
-- name    : SharpIntermediateSubgroupBounds.layer_card_bound_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:52:24.5102+00:00
-- url     : https://prove2.me/theorems/ba60541e-e992-5f1f-bba5-039b139a9902
-- title:
--   Sharp Intermediate Subgroup Bounds: layer card bound nat
-- statement:
--   Denominator-cleared exact layer bound (Corollary 3.1).
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L455-L476
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L455-L476

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

theorem SharpIntermediateSubgroupBounds.layer_card_bound_nat {H : Subgroup G} (hn : 1 < H.index)
    {q r m : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac)
    (hmi : m < q ^ (r + 1)) :
    gammaNum q r * (Nat.card (layer H m) * m ^ r) ≤
      gammaDen q r * H.index ^ r := by sorry
