-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_band_card_bound
-- name    : SharpIntermediateSubgroupBounds.band_card_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:45:35.936487+00:00
-- url     : https://prove2.me/theorems/bdbfc4d7-7d96-4ac9-9a83-ac04b0f63026
-- title:
--   Sharp Intermediate Subgroup Bounds: band card bound
-- statement:
--   Division form of the band-cardinality bound.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L214-L234
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L214-L234

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

theorem SharpIntermediateSubgroupBounds.band_card_bound {H : Subgroup G} (hn : 1 < H.index)
    {q : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) (r : ℕ) :
    (Nat.card (band H q r) : ℚ) ≤
      (H.index : ℚ) ^ r /
        (gammaQ q r * (q : ℚ) ^ (r * r)) := by sorry
