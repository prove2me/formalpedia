-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_intermediate_unique_band
-- name    : SharpIntermediateSubgroupBounds.intermediate_unique_band
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:52:20.243826+00:00
-- url     : https://prove2.me/theorems/5dff9c3d-598e-5cfe-85fb-3853a8c9313e
-- title:
--   Sharp Intermediate Subgroup Bounds: intermediate unique band
-- statement:
--   Every intermediate subgroup lies in a unique band through
--   `floor(log_q [G:H])`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L306-L322
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean#L306-L322

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

theorem SharpIntermediateSubgroupBounds.intermediate_unique_band (H : Subgroup G) (q : ℕ)
    (hn : 1 < H.index) (hq : 1 < q) (K : interval H) :
    ∃! r : Fin (Nat.log q H.index + 1),
      q ^ (r : ℕ) ≤ H.relIndex K.1 ∧
        H.relIndex K.1 < q ^ ((r : ℕ) + 1) := by sorry
