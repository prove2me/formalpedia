-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_branchMessage_eq_empty_iff
-- name    : TreeStack.OrientedBranch.branchMessage_eq_empty_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:18:03.78968+00:00
-- url     : https://prove2.me/theorems/22989430-f317-5eed-8da3-b157eb29ece1
-- title:
--   Oriented Branch: branch Message eq empty iff
-- statement:
--   Exact empty-state classification for branch messages.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Message.lean#L98-L107
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Message.lean#L98-L107

import Mathlib
import Definitions.Def_TreeStack_Transfer
import Definitions.Def_TreeStack_Branch
import Definitions.Def_TreeStack_Message
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.branchMessage_eq_empty_iff
    (C : Configuration V) (B : OrientedBranch T) :
    branchMessage C B = EMPTY ↔ ¬ B.Occupied C := by sorry
