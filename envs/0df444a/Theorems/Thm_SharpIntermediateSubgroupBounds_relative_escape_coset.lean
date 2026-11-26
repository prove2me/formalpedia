-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_relative_escape_coset
-- name    : SharpIntermediateSubgroupBounds.relative_escape_coset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:42:52.259606+00:00
-- url     : https://prove2.me/theorems/72da69e6-918d-41cd-b02b-53dd4ab440d4
-- title:
--   Sharp Intermediate Subgroup Bounds: relative escape coset
-- statement:
--   **Relative escape for literal coset tuples (Proposition 2.3).**
--   No normality hypothesis is imposed on `H`: the quotient here is the type
--   of left cosets for the subgroup `H.subgroupOf K`.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L914-L950
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L914-L950

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

theorem SharpIntermediateSubgroupBounds.relative_escape_coset {H K : Subgroup G}
    (hn : 1 < H.index) (hHK : H ≤ K) {r : ℕ}
    (hhi : H.relIndex K < H.index.minFac ^ (r + 1)) :
    gammaQ H.index.minFac r * (H.relIndex K : ℚ) ^ r ≤
      (Nat.card (CosetRelGen H K r) : ℚ) := by sorry
