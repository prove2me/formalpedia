-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_band_raw_sum_bound
-- name    : SharpIntermediateSubgroupBounds.band_raw_sum_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:45:24.61413+00:00
-- url     : https://prove2.me/theorems/0ab2132f-1b31-457d-bda3-255b2ab74809
-- title:
--   Sharp Intermediate Subgroup Bounds: band raw sum bound
-- statement:
--   Summed raw-tuple escape bound before cancellation of `|H|^r`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L107-L121
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L107-L121

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

theorem SharpIntermediateSubgroupBounds.band_raw_sum_bound {H : Subgroup G} (hn : 1 < H.index)
    {q r : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) :
    gammaQ q r *
        (∑ K : band H q r, (Nat.card K.1 : ℚ) ^ r) ≤
      (Nat.card G : ℚ) ^ r := by sorry
