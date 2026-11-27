-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_ambientLeaves_eq_leafVertices_of_root_not_leaf
-- name    : TreeStack.OrientedBranch.ambientLeaves_eq_leafVertices_of_root_not_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:55.09889+00:00
-- url     : https://prove2.me/theorems/a72b9c2e-6386-54e5-badf-c85bfc8daabc
-- title:
--   Oriented Branch: ambient Leaves eq leaf Vertices of root not leaf
-- statement:
--   The Oriented Branch construction uses the ambient Leaves eq leaf Vertices of root not leaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L362-L371
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L362-L371

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.ambientLeaves_eq_leafVertices_of_root_not_leaf
    (T : FiniteTree V) (r : V)
    (hNotLeaf : T.graph.degree r ≠ 1) :
    ambientLeaves (T := T) = leafVertices T r := by sorry
