-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_obstruction_score_root_of_parent_score_zero
-- name    : TreeStack.OrientedBranch.obstruction_score_root_of_parent_score_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:51:17.975956+00:00
-- url     : https://prove2.me/theorems/47b8a872-df30-5fcc-b79f-aa34f7e31fe7
-- title:
--   Oriented Branch: obstruction score root of parent score zero
-- statement:
--   Zero score propagates from the parent of a descendant obstruction branch
--   to that branch root.  The proof uses the exact reverse-side effective input,
--   so no executable task is ever introduced for an empty branch.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L846-L959
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L846-L959

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.obstruction_score_root_of_parent_score_zero
    (r : V) (B : OrientedBranch T)
    (hAway : r ∉ B.vertices)
    (hParent :
      score T (obstruction T r) B.parent = 0) :
    score T (obstruction T r) B.root = 0 := by sorry
