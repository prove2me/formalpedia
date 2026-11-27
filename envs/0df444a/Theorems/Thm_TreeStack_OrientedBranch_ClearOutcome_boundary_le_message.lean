-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_ClearOutcome_boundary_le_message
-- name    : TreeStack.OrientedBranch.ClearOutcome.boundary_le_message
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:28:45.695415+00:00
-- url     : https://prove2.me/theorems/967980a3-f4f7-46c0-b7f4-5307afa03523
-- title:
--   Clear Outcome: boundary le message
-- statement:
--   Necessity half of the exact boundary invariant.  Any legal clearing of an
--   occupied branch leaves no more than its recursive message gain at the external
--   boundary.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2378-L2432
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2378-L2432

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

theorem TreeStack.OrientedBranch.ClearOutcome.boundary_le_message
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {D : Configuration V} {d : ℤ}
    (hOcc : B.Occupied C)
    (hMsg : branchMessage C B = some d)
    (hClear : B.ClearOutcome C q D) :
    (D B.parent : ℤ) ≤ (q : ℤ) + d := by sorry
