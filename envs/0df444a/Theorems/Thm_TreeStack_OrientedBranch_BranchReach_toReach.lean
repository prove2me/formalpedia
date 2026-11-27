-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_BranchReach_toReach
-- name    : TreeStack.OrientedBranch.BranchReach.toReach
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:35:46.395489+00:00
-- url     : https://prove2.me/theorems/a165fee8-c439-48af-9f39-f7e133e4ab0e
-- title:
--   Branch Reach: to Reach
-- statement:
--   A branch-local legal reach is in particular a global legal reach.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L320-L330
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L320-L330

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.BranchReach.toReach
    [DecidableEq V] (B : OrientedBranch T) {C D : Configuration V}
    (hreach : B.BranchReach C D) :
    Reach T.graph C D := by sorry
