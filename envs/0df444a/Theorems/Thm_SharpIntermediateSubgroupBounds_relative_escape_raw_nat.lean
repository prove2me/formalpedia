-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_relative_escape_raw_nat
-- name    : SharpIntermediateSubgroupBounds.relative_escape_raw_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:46.161351+00:00
-- url     : https://prove2.me/theorems/5c13edea-3d1f-42b8-9903-3b38cdecacd3
-- title:
--   Sharp Intermediate Subgroup Bounds: relative escape raw nat
-- statement:
--   Denominator-cleared natural-number form of relative escape.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L884-L909
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L884-L909

import Definitions.Def_SharpIntermediateSubgroupBounds_Tree
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupDecidableEq

theorem SharpIntermediateSubgroupBounds.relative_escape_raw_nat {H K : Subgroup G}
    (hn : 1 < H.index) (hHK : H ≤ K) {r : ℕ}
    (hhi : H.relIndex K < H.index.minFac ^ (r + 1)) :
    gammaNum H.index.minFac r * Nat.card K ^ r ≤
      gammaDen H.index.minFac r * Nat.card (RawRelGen H K r) := by sorry
