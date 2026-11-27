-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_tree_path_length_eq_dist
-- name    : TreeStack.OrientedBranch.tree_path_length_eq_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:50:27.413635+00:00
-- url     : https://prove2.me/theorems/a86ba12f-2b05-5f4a-9dd0-2f4339869987
-- title:
--   Oriented Branch: tree path length eq dist
-- statement:
--   In a tree, every path is the unique shortest path between its endpoints.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L168-L178
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L168-L178

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.tree_path_length_eq_dist {u v : V} (p : T.graph.Walk u v)
    (hp : p.IsPath) :
    p.length = T.graph.dist u v := by sorry
