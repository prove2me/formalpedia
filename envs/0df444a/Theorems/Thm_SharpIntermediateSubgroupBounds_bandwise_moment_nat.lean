-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_bandwise_moment_nat
-- name    : SharpIntermediateSubgroupBounds.bandwise_moment_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:45:24.397336+00:00
-- url     : https://prove2.me/theorems/15f82ec4-2121-4b41-97eb-c860bf27b78a
-- title:
--   Sharp Intermediate Subgroup Bounds: bandwise moment nat
-- statement:
--   Denominator-cleared natural-number form of the bandwise moment
--   theorem.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L161-L184
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L161-L184

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

theorem SharpIntermediateSubgroupBounds.bandwise_moment_nat {H : Subgroup G} (hn : 1 < H.index)
    {q : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) (r : ℕ) :
    gammaNum q r *
        (∑ K : band H q r, H.relIndex K.1 ^ r) ≤
      gammaDen q r * H.index ^ r := by sorry
