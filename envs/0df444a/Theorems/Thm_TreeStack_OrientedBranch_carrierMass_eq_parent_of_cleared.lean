-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_carrierMass_eq_parent_of_cleared
-- name    : TreeStack.OrientedBranch.carrierMass_eq_parent_of_cleared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:34:08.270142+00:00
-- url     : https://prove2.me/theorems/fe7781b2-47b3-4849-a57e-fe2406f344f9
-- title:
--   Oriented Branch: carrier Mass eq parent of cleared
-- statement:
--   The Oriented Branch construction uses the carrier Mass eq parent of cleared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1747-L1761
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1747-L1761

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

theorem TreeStack.OrientedBranch.carrierMass_eq_parent_of_cleared
    (B : OrientedBranch T) (D : Configuration V) (hClear : B.Cleared D) :
    B.carrierMass D = D B.parent := by sorry
