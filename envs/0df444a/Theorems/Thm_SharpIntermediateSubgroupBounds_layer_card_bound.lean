-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_layer_card_bound
-- name    : SharpIntermediateSubgroupBounds.layer_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:52:35.567833+00:00
-- url     : https://prove2.me/theorems/4f887c94-83d3-514b-8010-9308b96b83e6
-- title:
--   Sharp Intermediate Subgroup Bounds: layer card bound
-- statement:
--   Literal division form of the exact-layer clause of Corollary 3.1.
--   The hypotheses place the fixed index `m` in band `r`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L480-L495
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L480-L495

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

theorem SharpIntermediateSubgroupBounds.layer_card_bound {H : Subgroup G} (hn : 1 < H.index)
    {q r m : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac)
    (hlo : q ^ r ≤ m) (hhi : m < q ^ (r + 1)) :
    (Nat.card (layer H m) : ℚ) ≤
      (H.index : ℚ) ^ r /
        (gammaQ q r * (m : ℚ) ^ r) := by sorry
