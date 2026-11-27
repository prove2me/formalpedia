-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_childBranch_card_lt
-- name    : TreeStack.OrientedBranch.childBranch_card_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:10:14.631195+00:00
-- url     : https://prove2.me/theorems/6ae3adcb-b987-53d3-88e4-297137abfc43
-- title:
--   Oriented Branch: child Branch card lt
-- statement:
--   Child-branch cardinality strictly decreases relative to the parent branch.
--   This is the recursion measure needed for branch messages.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L184-L187
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L184-L187

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.childBranch_card_lt (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).card < B.card := by sorry
