-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_branchMessage_eq_some_of_occupied
-- name    : TreeStack.OrientedBranch.branchMessage_eq_some_of_occupied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:17:57.414315+00:00
-- url     : https://prove2.me/theorems/ec226f2b-765b-59a8-991a-f82d9b25af60
-- title:
--   Oriented Branch: branch Message eq some of occupied
-- statement:
--   The Oriented Branch construction uses the branch Message eq some of occupied property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Message.lean#L91-L95
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Message.lean#L91-L95

import Mathlib
import Definitions.Def_TreeStack_Transfer
import Definitions.Def_TreeStack_Branch
import Definitions.Def_TreeStack_Message
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.branchMessage_eq_some_of_occupied
    (C : Configuration V) (B : OrientedBranch T) (hB : B.Occupied C) :
    branchMessage C B = some (F (effectiveInput C B)) := by sorry
