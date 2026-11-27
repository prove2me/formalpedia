-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_obstruction_scores_zero_on_vertices
-- name    : TreeStack.OrientedBranch.obstruction_scores_zero_on_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:52:37.060869+00:00
-- url     : https://prove2.me/theorems/ffca4451-5e48-477a-be16-b95b16a8827b
-- title:
--   Oriented Branch: obstruction scores zero on vertices
-- statement:
--   Once the parent score is zero, zero score propagates recursively through
--   every vertex of a descendant obstruction branch.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1284-L1311
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1284-L1311

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.obstruction_scores_zero_on_vertices
    (r : V) (B : OrientedBranch T)
    (hAway : r ∉ B.vertices)
    (hParent :
      score T (obstruction T r) B.parent = 0) :
    ∀ x ∈ B.vertices,
      score T (obstruction T r) x = 0 := by sorry
