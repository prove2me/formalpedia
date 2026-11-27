-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_no_child_of_degree_one
-- name    : TreeStack.OrientedBranch.no_child_of_degree_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:46:57.038527+00:00
-- url     : https://prove2.me/theorems/f318ba68-75ef-42c5-9730-d7ecae70280d
-- title:
--   Oriented Branch: no child of degree one
-- statement:
--   A degree-one branch root has no genuine child besides its boundary parent.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L139-L146
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L139-L146

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.no_child_of_degree_one (B : OrientedBranch T)
    (hLeaf : T.graph.degree B.root = 1) (v : V) :
    ¬ (T.graph.Adj B.root v ∧ v ≠ B.parent) := by sorry
