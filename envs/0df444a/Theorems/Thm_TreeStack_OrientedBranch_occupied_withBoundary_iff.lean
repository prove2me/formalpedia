-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_occupied_withBoundary_iff
-- name    : TreeStack.OrientedBranch.occupied_withBoundary_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:32:37.497468+00:00
-- url     : https://prove2.me/theorems/3581cd49-785d-4557-aa60-85d1193af43c
-- title:
--   Oriented Branch: occupied with Boundary iff
-- statement:
--   The Oriented Branch construction uses the occupied with Boundary iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L786-L793
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L786-L793

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

theorem TreeStack.OrientedBranch.occupied_withBoundary_iff (B : OrientedBranch T)
    (C : Configuration V) (q : ℕ) :
    B.Occupied (B.withBoundary C q) ↔ B.Occupied C := by sorry
