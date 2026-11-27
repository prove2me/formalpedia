-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_vertices_eq_singleton_of_degree_one
-- name    : TreeStack.OrientedBranch.vertices_eq_singleton_of_degree_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:49:55.229133+00:00
-- url     : https://prove2.me/theorems/13c72af4-9873-4933-bb88-8156b3c42f91
-- title:
--   Oriented Branch: vertices eq singleton of degree one
-- statement:
--   A degree-one oriented branch consists only of its root.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L181-L198
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L181-L198

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.vertices_eq_singleton_of_degree_one (B : OrientedBranch T)
    (hLeaf : T.graph.degree B.root = 1) :
    B.vertices = {B.root} := by sorry
