-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_signature_branchFlux_bounds
-- name    : TreeStack.OrientedBranch.signature_branchFlux_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:14.716434+00:00
-- url     : https://prove2.me/theorems/68842974-1f77-5094-b303-e18b8a5f91f9
-- title:
--   Oriented Branch: signature branch Flux bounds
-- statement:
--   Recursive signature bound.  Every genuine child contributes its recursive
--   message minus a nonnegative multiple of three; an empty child contributes only
--   such a three-step loss.  At an occupied branch the resulting boundary flux is
--   bounded by the recursive transfer and has the same residue modulo three.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2181-L2372
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2181-L2372

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

theorem TreeStack.OrientedBranch.signature_branchFlux_bounds
    (m : MoveSignature T) (C : Configuration V) (B : OrientedBranch T)
    (hClears : MoveSignature.Clears m C B)
    (hCausal :
      ∀ A : OrientedBranch T,
        A.vertices ⊆ B.vertices →
        A.Occupied C →
        MoveSignature.CausalOutward m A) :
    (B.Occupied C →
      MoveSignature.boundaryFlux m B ≤ F (effectiveInput C B) ∧
      MoveSignature.boundaryFlux m B % 3 =
        F (effectiveInput C B) % 3) ∧
    (¬ B.Occupied C →
      ∃ k : ℕ,
        MoveSignature.boundaryFlux m B = -3 * (k : ℤ)) := by sorry
