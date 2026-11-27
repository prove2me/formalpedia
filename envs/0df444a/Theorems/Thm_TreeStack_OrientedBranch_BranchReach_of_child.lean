-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_BranchReach_of_child
-- name    : TreeStack.OrientedBranch.BranchReach.of_child
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:32:19.172839+00:00
-- url     : https://prove2.me/theorems/9b726e8f-eba1-51e5-b9ea-ac02b71f2b8b
-- title:
--   Branch Reach: of child
-- statement:
--   A legal sequence inside a genuine child carrier is also a legal sequence
--   inside the parent branch carrier.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L690-L704
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L690-L704

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

theorem TreeStack.OrientedBranch.BranchReach.of_child
    (B : OrientedBranch T) (c : B.Child)
    {C D : Configuration V}
    (hreach : (B.childBranch c).BranchReach C D) :
    B.BranchReach C D := by sorry
