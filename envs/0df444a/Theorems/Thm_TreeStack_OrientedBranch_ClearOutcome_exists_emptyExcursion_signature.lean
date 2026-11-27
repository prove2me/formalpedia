-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_ClearOutcome_exists_emptyExcursion_signature
-- name    : TreeStack.OrientedBranch.ClearOutcome.exists_emptyExcursion_signature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:38:56.006802+00:00
-- url     : https://prove2.me/theorems/29912390-6abc-5a93-a64d-c7905cf70e6c
-- title:
--   Clear Outcome: exists empty Excursion signature
-- statement:
--   Every legal empty-branch excursion has exact boundary flux -3k for some
--   nonnegative integer k.  The branch remains EMPTY at the message level; zero is
--   used here only as the omitted formal gain in this excursion calculation.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1923-L1978
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1923-L1978

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

theorem TreeStack.OrientedBranch.ClearOutcome.exists_emptyExcursion_signature
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {D : Configuration V} (hEmpty : ¬ B.Occupied C)
    (hClear : B.ClearOutcome C q D) :
    ∃ m : MoveSignature T,
      MoveSignature.EmptyExcursion m B ∧
      (D B.parent : ℤ) =
        (q : ℤ) + MoveSignature.boundaryFlux m B ∧
      ∃ k : ℤ, 0 ≤ k ∧ MoveSignature.boundaryFlux m B = -3 * k := by sorry
