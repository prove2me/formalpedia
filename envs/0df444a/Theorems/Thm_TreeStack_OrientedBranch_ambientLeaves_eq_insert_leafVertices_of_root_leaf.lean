-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_ambientLeaves_eq_insert_leafVertices_of_root_leaf
-- name    : TreeStack.OrientedBranch.ambientLeaves_eq_insert_leafVertices_of_root_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:44.640063+00:00
-- url     : https://prove2.me/theorems/70915d68-60d6-50a3-8286-d52499b540b2
-- title:
--   Oriented Branch: ambient Leaves eq insert leaf Vertices of root leaf
-- statement:
--   The Oriented Branch construction uses the ambient Leaves eq insert leaf Vertices of root leaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L351-L360
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L351-L360

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.ambientLeaves_eq_insert_leafVertices_of_root_leaf
    (T : FiniteTree V) (r : V)
    (hLeaf : T.graph.degree r = 1) :
    ambientLeaves (T := T) = insert r (leafVertices T r) := by sorry
