-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_MoveSignature_incoming_parent_eq_boundary
-- name    : TreeStack.OrientedBranch.MoveSignature.incoming_parent_eq_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:27:38.057809+00:00
-- url     : https://prove2.me/theorems/8dfe6ce3-151d-48ab-8416-fc0b2d9031b9
-- title:
--   Move Signature: incoming parent eq boundary
-- statement:
--   The Move Signature construction uses the incoming parent eq boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1601-L1619
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1601-L1619

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

theorem TreeStack.OrientedBranch.MoveSignature.incoming_parent_eq_boundary
    (B : OrientedBranch T) (m : MoveSignature T)
    (hm : MoveSignature.SupportedOn m B) :
    m.incoming B.parent = m.count B.root B.parent := by sorry
