-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_dist_parent_eq_root_dist_add_one
-- name    : TreeStack.OrientedBranch.dist_parent_eq_root_dist_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:45:59.913192+00:00
-- url     : https://prove2.me/theorems/f555c425-eb2e-43e8-b68b-cb22229b62a5
-- title:
--   Oriented Branch: dist parent eq root dist add one
-- statement:
--   Every vertex of an oriented branch is one edge farther from the external
--   parent than from the branch root.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L204-L243
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L204-L243

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.dist_parent_eq_root_dist_add_one
    (B : OrientedBranch T) {x : V} (hx : x ∈ B.vertices) :
    T.graph.dist B.parent x =
      T.graph.dist B.root x + 1 := by sorry
