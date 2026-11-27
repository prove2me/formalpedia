-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_sourceFiber_dist_le_of_boundary_depth
-- name    : TreeStack.OrientedBranch.sourceFiber_dist_le_of_boundary_depth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:56.110866+00:00
-- url     : https://prove2.me/theorems/98a8ed6b-f106-48a3-a5ba-2d4a8d2a6cec
-- title:
--   Oriented Branch: source Fiber dist le of boundary depth
-- statement:
--   If the depth of the first source to its boundary endpoint plus the crossing
--   edge dominates the depth of the second source to its endpoint, then the first
--   source is at least as far from every vertex in the second fibre as the second
--   source is.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L662-L686
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L662-L686

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.sourceFiber_dist_le_of_boundary_depth
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r s a b v : V}
    (hrs : r ≠ s)
    (ha : a ∈ auxSourceFiber C ambientRoot hScores r)
    (hb : b ∈ auxSourceFiber C ambientRoot hScores s)
    (hadj : T.graph.Adj a b)
    (hDepth :
      T.graph.dist s b ≤ T.graph.dist r a + 1)
    (hv : v ∈ auxSourceFiber C ambientRoot hScores s) :
    T.graph.dist s v ≤ T.graph.dist r v := by sorry
