-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_dist_root_eq_child_dist_add_one
-- name    : TreeStack.OrientedBranch.dist_root_eq_child_dist_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:50:40.574318+00:00
-- url     : https://prove2.me/theorems/648c74ed-6389-4aab-b7c7-4c0fbc753263
-- title:
--   Oriented Branch: dist root eq child dist add one
-- statement:
--   Distances into a genuine child branch increase by exactly one when
--   measured from the parent-branch root.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L247-L253
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L247-L253

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.dist_root_eq_child_dist_add_one
    (B : OrientedBranch T) (c : B.Child) {x : V}
    (hx : x ∈ (B.childBranch c).vertices) :
    T.graph.dist B.root x =
      T.graph.dist c.vertex x + 1 := by sorry
