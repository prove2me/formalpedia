-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_exists_heightDominatingRoot_union_of_adj
-- name    : TreeStack.OrientedBranch.exists_heightDominatingRoot_union_of_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:34.745806+00:00
-- url     : https://prove2.me/theorems/0079dd62-e664-4a13-a7ab-823d5d4ada10
-- title:
--   Oriented Branch: exists height Dominating Root union of adj
-- statement:
--   Merge two disjoint connected dominated carriers across one boundary edge.
--   The root on the side whose boundary depth is large enough dominates the whole
--   union; if that comparison fails, the opposite root necessarily works.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L277-L326
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L277-L326

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.exists_heightDominatingRoot_union_of_adj
    (h : V → ℕ)
    {A B : Finset V}
    (hAConn : TreePathConnected (T := T) A)
    (hBConn : TreePathConnected (T := T) B)
    (hDisj : Disjoint A B)
    {a b r s : V}
    (ha : a ∈ A) (hb : b ∈ B)
    (hadj : T.graph.Adj a b)
    (hADom : HeightDominated (T := T) h A r)
    (hBDom : HeightDominated (T := T) h B s) :
    ∃ t : V,
      HeightDominated (T := T) h (A ∪ B) t := by sorry
