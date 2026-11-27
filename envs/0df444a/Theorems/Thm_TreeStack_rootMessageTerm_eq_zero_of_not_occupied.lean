-- Prove2me | Theorems.Thm_TreeStack_rootMessageTerm_eq_zero_of_not_occupied
-- name    : TreeStack.rootMessageTerm_eq_zero_of_not_occupied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:35:14.039208+00:00
-- url     : https://prove2.me/theorems/1b02040b-6b48-543e-90b7-e37f6153a37c
-- title:
--   Tree Stack: root Message Term eq zero of not occupied
-- statement:
--   The Tree Stack construction uses the root Message Term eq zero of not occupied property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L236-L247
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L236-L247

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.rootMessageTerm_eq_zero_of_not_occupied
    (T : FiniteTree V) (C : Configuration V) (r : V) {u : V}
    (hu : ¬ IsOccupiedRootNeighbor T C r u) :
    rootMessageTerm T C r u = 0 := by sorry
