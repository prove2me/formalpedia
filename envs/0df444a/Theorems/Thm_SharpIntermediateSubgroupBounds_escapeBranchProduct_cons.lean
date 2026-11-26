-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
-- name    : SharpIntermediateSubgroupBounds.escapeBranchProduct_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:42:28.613901+00:00
-- url     : https://prove2.me/theorems/c3bcd191-9798-4967-810a-80ad506ce1f2
-- title:
--   Sharp Intermediate Subgroup Bounds: escape Branch Product cons
-- statement:
--   The Sharp Intermediate Subgroup Bounds construction uses the escape Branch Product cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L713-L719
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean#L713-L719

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

theorem SharpIntermediateSubgroupBounds.escapeBranchProduct_cons (K : Subgroup G) {r : ℕ}
    {s : EscapeState K} (x : EscapeChoice K s)
    (z : EscapePath K r (escapeNext K s x)) :
    BranchingTree.branchProduct (EscapeChoice K) (escapeNext K)
        (escapeCons K x z) =
      Fintype.card (EscapeChoice K s) *
        BranchingTree.branchProduct (EscapeChoice K) (escapeNext K) z := by sorry

attribute [defeq] SharpIntermediateSubgroupBounds.escapeBranchProduct_cons
