-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_bandwise_moment
-- name    : SharpIntermediateSubgroupBounds.bandwise_moment
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:43:58.144394+00:00
-- url     : https://prove2.me/theorems/31e6b0fc-29a9-4cd7-985a-c3e3fcca7098
-- title:
--   Sharp Intermediate Subgroup Bounds: bandwise moment
-- statement:
--   The bandwise moment theorem (Theorem 1.3), over the exact field `ℚ`.
--   The parameterized form includes the least-prime choice and the universal
--   choice `q = 2`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L126-L157
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L126-L157

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

theorem SharpIntermediateSubgroupBounds.bandwise_moment {H : Subgroup G} (hn : 1 < H.index)
    {q : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) (r : ℕ) :
    gammaQ q r *
        (∑ K : band H q r, (H.relIndex K.1 : ℚ) ^ r) ≤
      (H.index : ℚ) ^ r := by sorry
