-- Prove2me | Theorems.Thm_TreeStack_MoveSignature_outgoing_extend
-- name    : TreeStack.MoveSignature.outgoing_extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:28:43.861422+00:00
-- url     : https://prove2.me/theorems/88c02d34-0baa-43d6-806c-7bd780e9e5e0
-- title:
--   Move Signature: outgoing extend
-- statement:
--   The Move Signature construction uses the outgoing extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L74-L82
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L74-L82

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.MoveSignature
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.MoveSignature.outgoing_extend [DecidableEq V]
    (m : MoveSignature T) {u v : V} (huv : T.graph.Adj u v) (w : V) :
    (m.extend u v huv).outgoing w =
      m.outgoing w + if w = u then 1 else 0 := by sorry
