-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_branchMessage_ne_empty_of_occupied
-- name    : TreeStack.OrientedBranch.branchMessage_ne_empty_of_occupied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:18:06.226865+00:00
-- url     : https://prove2.me/theorems/452b63f3-7e5a-5725-b795-48723ed190e6
-- title:
--   Oriented Branch: branch Message ne empty of occupied
-- statement:
--   A configuration-nonempty branch always has an integer message.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Message.lean#L110-L114
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Message.lean#L110-L114

import Mathlib
import Definitions.Def_TreeStack_Transfer
import Definitions.Def_TreeStack_Branch
import Definitions.Def_TreeStack_Message
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.branchMessage_ne_empty_of_occupied
    (C : Configuration V) (B : OrientedBranch T) (hB : B.Occupied C) :
    branchMessage C B ≠ EMPTY := by sorry
