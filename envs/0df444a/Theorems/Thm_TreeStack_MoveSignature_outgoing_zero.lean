-- Prove2me | Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
-- name    : TreeStack.MoveSignature.outgoing_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:26:34.166812+00:00
-- url     : https://prove2.me/theorems/5f46100c-a011-4ba6-84e5-8596bf5a020d
-- title:
--   Move Signature: outgoing zero
-- statement:
--   The Move Signature construction uses the outgoing zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L55-L57
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L55-L57

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.MoveSignature
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.MoveSignature.outgoing_zero (v : V) :
    (zero T).outgoing v = 0 := by sorry
