-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_signedCarrierMass_eq_parent_of_cleared
-- name    : TreeStack.OrientedBranch.signedCarrierMass_eq_parent_of_cleared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:34:35.448341+00:00
-- url     : https://prove2.me/theorems/289194d7-69ff-4e88-8a0b-4bf718116969
-- title:
--   Oriented Branch: signed Carrier Mass eq parent of cleared
-- statement:
--   The Oriented Branch construction uses the signed Carrier Mass eq parent of cleared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1885-L1905
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1885-L1905

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

theorem TreeStack.OrientedBranch.signedCarrierMass_eq_parent_of_cleared
    (B : OrientedBranch T) (D : Configuration V) (hClear : B.Cleared D) :
    B.signedCarrierMass D = D B.parent := by sorry
