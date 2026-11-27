-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_childMessageTerm_eq_zero_of_not_occupiedChild
-- name    : TreeStack.OrientedBranch.childMessageTerm_eq_zero_of_not_occupiedChild
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:32:51.083884+00:00
-- url     : https://prove2.me/theorems/d3ec4016-ba46-532c-b7fa-a7bb3797fcbe
-- title:
--   Oriented Branch: child Message Term eq zero of not occupied Child
-- statement:
--   The Oriented Branch construction uses the child Message Term eq zero of not occupied Child property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L862-L874
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L862-L874

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

theorem TreeStack.OrientedBranch.childMessageTerm_eq_zero_of_not_occupiedChild
    (B : OrientedBranch T) (C : Configuration V) {v : V}
    (hv : ¬ B.IsOccupiedChildVertex C v) :
    B.childMessageTerm C v = 0 := by sorry
