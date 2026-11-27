-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_dist_eq_dist_add_one_add_dist_of_adj_disjoint_carriers
-- name    : TreeStack.OrientedBranch.dist_eq_dist_add_one_add_dist_of_adj_disjoint_carriers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:25.024556+00:00
-- url     : https://prove2.me/theorems/e2077d72-c758-5ad2-b094-4672b5c0616e
-- title:
--   Oriented Branch: dist eq dist add one add dist of adj disjoint carriers
-- statement:
--   Generic boundary additivity for two disjoint path-connected carriers.
--   Because the ambient graph is a tree, concatenating an internal path in the
--   first carrier, the crossing edge, and an internal path in the second carrier
--   is itself the unique simple path between the endpoints.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L159-L212
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L159-L212

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.dist_eq_dist_add_one_add_dist_of_adj_disjoint_carriers
    {A B : Finset V}
    (hA : TreePathConnected (T := T) A)
    (hB : TreePathConnected (T := T) B)
    (hDisj : Disjoint A B)
    {a b x y : V}
    (ha : a ∈ A) (hb : b ∈ B)
    (hadj : T.graph.Adj a b)
    (hx : x ∈ A) (hy : y ∈ B) :
    T.graph.dist x y =
      T.graph.dist x a + 1 + T.graph.dist b y := by sorry
