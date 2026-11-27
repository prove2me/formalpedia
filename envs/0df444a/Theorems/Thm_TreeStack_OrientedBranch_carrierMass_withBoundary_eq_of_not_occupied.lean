-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_carrierMass_withBoundary_eq_of_not_occupied
-- name    : TreeStack.OrientedBranch.carrierMass_withBoundary_eq_of_not_occupied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:33:52.209773+00:00
-- url     : https://prove2.me/theorems/b57049cb-0326-461d-bcb2-35756fecab49
-- title:
--   Oriented Branch: carrier Mass with Boundary eq of not occupied
-- statement:
--   The Oriented Branch construction uses the carrier Mass with Boundary eq of not occupied property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1728-L1745
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1728-L1745

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

theorem TreeStack.OrientedBranch.carrierMass_withBoundary_eq_of_not_occupied
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    (hEmpty : ¬ B.Occupied C) :
    B.carrierMass (B.withBoundary C q) = q := by sorry
