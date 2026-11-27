-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_MoveSignature_extend_supportedOn
-- name    : TreeStack.OrientedBranch.MoveSignature.extend_supportedOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:33:48.534078+00:00
-- url     : https://prove2.me/theorems/e32a1462-2ca1-4519-b1cf-6e71ecdcbe69
-- title:
--   Move Signature: extend supported On
-- statement:
--   The Move Signature construction uses the extend supported On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1503-L1513
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1503-L1513

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

theorem TreeStack.OrientedBranch.MoveSignature.extend_supportedOn
    (B : OrientedBranch T) (m : MoveSignature T)
    {u v : V} (huv : T.graph.Adj u v)
    (hm : MoveSignature.SupportedOn m B) (hu : u ∈ B.carrier) (hv : v ∈ B.carrier) :
    MoveSignature.SupportedOn (m.extend u v huv) B := by sorry
