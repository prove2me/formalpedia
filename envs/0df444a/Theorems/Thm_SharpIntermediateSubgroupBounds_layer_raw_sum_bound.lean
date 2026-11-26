-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_layer_raw_sum_bound
-- name    : SharpIntermediateSubgroupBounds.layer_raw_sum_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:45:53.849085+00:00
-- url     : https://prove2.me/theorems/cc892152-572c-452d-80ec-58ae84050fb1
-- title:
--   Sharp Intermediate Subgroup Bounds: layer raw sum bound
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the layer raw sum bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L393-L408
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L393-L408

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

theorem SharpIntermediateSubgroupBounds.layer_raw_sum_bound {H : Subgroup G} (hn : 1 < H.index)
    {q r m : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac)
    (hmi : m < q ^ (r + 1)) :
    gammaQ q r *
        (∑ K : layer H m, (Nat.card K.1 : ℚ) ^ r) ≤
      (Nat.card G : ℚ) ^ r := by sorry
