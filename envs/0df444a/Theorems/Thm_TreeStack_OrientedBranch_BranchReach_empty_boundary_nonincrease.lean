-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_BranchReach_empty_boundary_nonincrease
-- name    : TreeStack.OrientedBranch.BranchReach.empty_boundary_nonincrease
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:33:36.637378+00:00
-- url     : https://prove2.me/theorems/84b0afda-607c-5016-b7dd-745ac53e80d4
-- title:
--   Branch Reach: empty boundary nonincrease
-- statement:
--   A legal initially empty excursion cannot increase the boundary pile.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1764-L1773
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1764-L1773

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]

theorem TreeStack.OrientedBranch.BranchReach.empty_boundary_nonincrease
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {D : Configuration V} (hEmpty : ¬ B.Occupied C)
    (hreach : B.BranchReach (B.withBoundary C q) D)
    (hClear : B.Cleared D) :
    D B.parent ≤ q := by sorry
