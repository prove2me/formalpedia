-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_signedCarrierMass_move
-- name    : TreeStack.OrientedBranch.signedCarrierMass_move
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:33:45.230825+00:00
-- url     : https://prove2.me/theorems/e6075663-e71b-5368-be07-2153a0b2f896
-- title:
--   Oriented Branch: signed Carrier Mass move
-- statement:
--   The Oriented Branch construction uses the signed Carrier Mass move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1816-L1840
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1816-L1840

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

theorem TreeStack.OrientedBranch.signedCarrierMass_move (B : OrientedBranch T)
    (C : Configuration V) {u v : V} (huv : T.graph.Adj u v)
    (hu : 2 ≤ C u) (huB : u ∈ B.carrier) (hvB : v ∈ B.carrier) :
    B.signedCarrierMass (move C u v) =
      B.signedCarrierMass C - 3 * B.boundaryParityWeight u := by sorry
