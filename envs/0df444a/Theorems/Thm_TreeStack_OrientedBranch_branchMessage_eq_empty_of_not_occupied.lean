-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_branchMessage_eq_empty_of_not_occupied
-- name    : TreeStack.OrientedBranch.branchMessage_eq_empty_of_not_occupied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:18:01.757871+00:00
-- url     : https://prove2.me/theorems/b13fca63-a705-5021-9a76-c9e91c1050e2
-- title:
--   Oriented Branch: branch Message eq empty of not occupied
-- statement:
--   The Oriented Branch construction uses the branch Message eq empty of not occupied property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Message.lean#L85-L89
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Message.lean#L85-L89

import Mathlib
import Definitions.Def_TreeStack_Transfer
import Definitions.Def_TreeStack_Branch
import Definitions.Def_TreeStack_Message
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.branchMessage_eq_empty_of_not_occupied
    (C : Configuration V) (B : OrientedBranch T) (hB : ¬ B.Occupied C) :
    branchMessage C B = EMPTY := by sorry
