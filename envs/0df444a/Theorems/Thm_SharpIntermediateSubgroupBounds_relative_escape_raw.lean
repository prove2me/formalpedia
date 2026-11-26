-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_relative_escape_raw
-- name    : SharpIntermediateSubgroupBounds.relative_escape_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:42:25.879975+00:00
-- url     : https://prove2.me/theorems/576990af-20f5-5ec7-9e19-50285c1e0947
-- title:
--   Sharp Intermediate Subgroup Bounds: relative escape raw
-- statement:
--   Relative escape theorem, in exact rational form for raw element
--   tuples.  This is the coset-free form used by packing.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L866-L881
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L866-L881

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

theorem SharpIntermediateSubgroupBounds.relative_escape_raw {H K : Subgroup G}
    (hn : 1 < H.index) (hHK : H ≤ K) {r : ℕ}
    (hhi : H.relIndex K < H.index.minFac ^ (r + 1)) :
    gammaQ H.index.minFac r * (Nat.card K : ℚ) ^ r ≤
      (Nat.card (RawRelGen H K r) : ℚ) := by sorry
