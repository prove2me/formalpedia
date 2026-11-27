-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_ClearOutcome_no_positive_boundary_of_message_nonpos
-- name    : TreeStack.OrientedBranch.ClearOutcome.no_positive_boundary_of_message_nonpos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:34:49.466181+00:00
-- url     : https://prove2.me/theorems/a67b8119-761f-5bd4-8fcc-f5c0097931c5
-- title:
--   Clear Outcome: no positive boundary of message nonpos
-- statement:
--   If the boundary plus recursive message is nonpositive, no legal clearing
--   can leave a positive boundary pile.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2436-L2449
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2436-L2449

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

theorem TreeStack.OrientedBranch.ClearOutcome.no_positive_boundary_of_message_nonpos
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {d : ℤ}
    (hOcc : B.Occupied C)
    (hMsg : branchMessage C B = some d)
    (hNonpos : (q : ℤ) + d ≤ 0) :
    ¬ ∃ D : Configuration V,
      B.ClearOutcome C q D ∧ 0 < D B.parent := by sorry
