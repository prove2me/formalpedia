-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_escapePathToRawRelGen_injective
-- name    : SharpIntermediateSubgroupBounds.escapePathToRawRelGen_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:45:07.202705+00:00
-- url     : https://prove2.me/theorems/469840f7-bb4d-5a66-9538-7856988f46f2
-- title:
--   Sharp Intermediate Subgroup Bounds: escape Path To Raw Rel Gen injective
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the escape Path To Raw Rel Gen injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L856-L862
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L856-L862

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

theorem SharpIntermediateSubgroupBounds.escapePathToRawRelGen_injective {H K : Subgroup G}
    (hHK : H ≤ K) {r : ℕ}
    (hhi : H.relIndex K < H.index.minFac ^ (r + 1)) :
    Function.Injective (escapePathToRawRelGen hHK hhi) := by sorry
