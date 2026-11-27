-- Prove2me | Theorems.Thm_TreeStack_MoveSignature_extend_count_same
-- name    : TreeStack.MoveSignature.extend_count_same
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:26:40.098225+00:00
-- url     : https://prove2.me/theorems/5eb1ad19-e38e-470d-89bc-26ea7100304e
-- title:
--   Move Signature: extend count same
-- statement:
--   The Move Signature construction uses the extend count same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L59-L62
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L59-L62

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.MoveSignature
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.MoveSignature.extend_count_same [DecidableEq V]
    (m : MoveSignature T) {u v : V} (huv : T.graph.Adj u v) :
    (m.extend u v huv).count u v = m.count u v + 1 := by sorry
