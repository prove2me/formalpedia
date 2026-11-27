-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_ClearOutcome_exists_feasibleClearing_signature
-- name    : TreeStack.OrientedBranch.ClearOutcome.exists_feasibleClearing_signature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:38:36.349463+00:00
-- url     : https://prove2.me/theorems/d63a207f-2669-59ea-b254-bbd904d2cc12
-- title:
--   Clear Outcome: exists feasible Clearing signature
-- statement:
--   Every legal clearing of an initially occupied branch yields a genuine
--   feasible clearing signature, and the final boundary pile is exactly the
--   initial boundary pile plus the signature's boundary flux.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1644-L1680
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1644-L1680

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

theorem TreeStack.OrientedBranch.ClearOutcome.exists_feasibleClearing_signature
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {D : Configuration V} (hOcc : B.Occupied C)
    (hClear : B.ClearOutcome C q D) :
    ∃ m : MoveSignature T,
      MoveSignature.FeasibleClearing m C B ∧
      (D B.parent : ℤ) =
        (q : ℤ) + MoveSignature.boundaryFlux m B := by sorry
