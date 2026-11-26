-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_escapePath_card_lower_bound
-- name    : SharpIntermediateSubgroupBounds.escapePath_card_lower_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:44:58.506462+00:00
-- url     : https://prove2.me/theorems/ee74c8db-93a0-517e-b02d-0d9c5249aa49
-- title:
--   Sharp Intermediate Subgroup Bounds: escape Path card lower bound
-- statement:
--   The escape tree has at least the Euler-factor fraction of all raw
--   tuples as leaves.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L837-L845
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L837-L845

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

theorem SharpIntermediateSubgroupBounds.escapePath_card_lower_bound {H K : Subgroup G}
    (hn : 1 < H.index) (hHK : H ≤ K) (r : ℕ) :
    gammaQ H.index.minFac r * (Nat.card K : ℚ) ^ r ≤
      (Fintype.card (EscapePath K r ⟨H, hHK⟩) : ℚ) := by sorry
