-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_signedCarrierMass_withBoundary_eq_of_not_occupied
-- name    : TreeStack.OrientedBranch.signedCarrierMass_withBoundary_eq_of_not_occupied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:34:17.655198+00:00
-- url     : https://prove2.me/theorems/d59c0b22-0dcc-5236-9aa3-ef7ebf7aff68
-- title:
--   Oriented Branch: signed Carrier Mass with Boundary eq of not occupied
-- statement:
--   The Oriented Branch construction uses the signed Carrier Mass with Boundary eq of not occupied property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1860-L1883
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1860-L1883

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

theorem TreeStack.OrientedBranch.signedCarrierMass_withBoundary_eq_of_not_occupied
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    (hEmpty : ¬ B.Occupied C) :
    B.signedCarrierMass (B.withBoundary C q) = q := by sorry
