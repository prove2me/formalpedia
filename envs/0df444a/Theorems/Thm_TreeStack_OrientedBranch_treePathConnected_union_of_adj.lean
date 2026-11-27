-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_treePathConnected_union_of_adj
-- name    : TreeStack.OrientedBranch.treePathConnected_union_of_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:26.056866+00:00
-- url     : https://prove2.me/theorems/c583e693-cba6-5392-b2e6-2fc69eae3c9b
-- title:
--   Oriented Branch: tree Path Connected union of adj
-- statement:
--   The union of two path-connected carriers joined by an ambient edge is
--   again path-connected.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L223-L272
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L223-L272

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.treePathConnected_union_of_adj
    {A B : Finset V}
    (hA : TreePathConnected (T := T) A)
    (hB : TreePathConnected (T := T) B)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (hadj : T.graph.Adj a b) :
    TreePathConnected (T := T) (A ∪ B) := by sorry
