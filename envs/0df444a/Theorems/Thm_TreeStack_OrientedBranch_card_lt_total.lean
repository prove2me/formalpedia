-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_card_lt_total
-- name    : TreeStack.OrientedBranch.card_lt_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:12:42.096897+00:00
-- url     : https://prove2.me/theorems/f1634cff-5c63-4f3f-bb31-d2509ba429ed
-- title:
--   Oriented Branch: card lt total
-- statement:
--   The branch-cardinality measure is strictly smaller than the whole tree.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L82-L85
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Branch.lean#L82-L85

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.card_lt_total (B : OrientedBranch T) :
    B.card < Fintype.card V := by sorry
