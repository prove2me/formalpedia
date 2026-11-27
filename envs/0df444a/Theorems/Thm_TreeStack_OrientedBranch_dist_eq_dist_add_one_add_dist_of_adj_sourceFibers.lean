-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_dist_eq_dist_add_one_add_dist_of_adj_sourceFibers
-- name    : TreeStack.OrientedBranch.dist_eq_dist_add_one_add_dist_of_adj_sourceFibers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:15.481479+00:00
-- url     : https://prove2.me/theorems/a52295d6-3ee1-4b4d-845a-e35e6b6cc2a0
-- title:
--   Oriented Branch: dist eq dist add one add dist of adj source Fibers
-- statement:
--   Across an edge joining two distinct source fibres, tree distance splits
--   exactly at that boundary edge.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L580-L643
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L580-L643

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.dist_eq_dist_add_one_add_dist_of_adj_sourceFibers
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r s a b x y : V}
    (hrs : r ≠ s)
    (ha : a ∈ auxSourceFiber C ambientRoot hScores r)
    (hb : b ∈ auxSourceFiber C ambientRoot hScores s)
    (hadj : T.graph.Adj a b)
    (hx : x ∈ auxSourceFiber C ambientRoot hScores r)
    (hy : y ∈ auxSourceFiber C ambientRoot hScores s) :
    T.graph.dist x y =
      T.graph.dist x a + 1 + T.graph.dist b y := by sorry
