-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_band_card_bound_nat
-- name    : SharpIntermediateSubgroupBounds.band_card_bound_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:52:03.487665+00:00
-- url     : https://prove2.me/theorems/f1520355-d201-55cb-b7f1-7476a44248ef
-- title:
--   Sharp Intermediate Subgroup Bounds: band card bound nat
-- statement:
--   Denominator-cleared band-cardinality bound (Corollary 3.1).
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L206-L211
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L206-L211

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

theorem SharpIntermediateSubgroupBounds.band_card_bound_nat {H : Subgroup G} (hn : 1 < H.index)
    {q : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) (r : ℕ) :
    gammaNum q r * (Nat.card (band H q r) * q ^ (r * r)) ≤
      gammaDen q r * H.index ^ r := by sorry
