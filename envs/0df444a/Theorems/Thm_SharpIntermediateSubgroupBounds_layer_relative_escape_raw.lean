-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_layer_relative_escape_raw
-- name    : SharpIntermediateSubgroupBounds.layer_relative_escape_raw
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:45:51.353617+00:00
-- url     : https://prove2.me/theorems/d92590bd-c2ac-447e-a86e-d2012bc67dd2
-- title:
--   Sharp Intermediate Subgroup Bounds: layer relative escape raw
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the layer relative escape raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L381-L391
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L381-L391

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

theorem SharpIntermediateSubgroupBounds.layer_relative_escape_raw {H : Subgroup G} (hn : 1 < H.index)
    {q r m : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac)
    (hmi : m < q ^ (r + 1)) (K : layer H m) :
    gammaQ q r * (Nat.card K.1 : ℚ) ^ r ≤
      (Nat.card (RawRelGen H K.1 r) : ℚ) := by sorry
