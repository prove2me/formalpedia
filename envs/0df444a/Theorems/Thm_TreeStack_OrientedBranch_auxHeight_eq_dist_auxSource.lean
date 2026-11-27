-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxHeight_eq_dist_auxSource
-- name    : TreeStack.OrientedBranch.auxHeight_eq_dist_auxSource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:14:18.468388+00:00
-- url     : https://prove2.me/theorems/8d4207e7-a0a1-501e-9e58-609e8047b094
-- title:
--   Oriented Branch: aux Height eq dist aux Source
-- statement:
--   Auxiliary height is a genuine tree distance from the canonical source.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L247-L268
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L247-L268

import Mathlib
import Definitions.Def_TreeStack_LeafSlack
import Definitions.Def_TreeStack_HeightSource
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxHeight_eq_dist_auxSource
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    auxHeight C ambientRoot hScores v =
      T.graph.dist (auxSource C ambientRoot hScores v) v := by sorry
