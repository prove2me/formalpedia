-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
-- name    : TreeStack.OrientedBranch.mem_occupiedChildTasks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:26:37.004668+00:00
-- url     : https://prove2.me/theorems/8cac64aa-afd5-5ab7-82ed-39c4cdd9635d
-- title:
--   Oriented Branch: mem occupied Child Tasks
-- statement:
--   The Oriented Branch construction uses the mem occupied Child Tasks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L912-L917
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L912-L917

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

theorem TreeStack.OrientedBranch.mem_occupiedChildTasks
    (B : OrientedBranch T) (C : Configuration V)
    (t : B.OccupiedChild C) :
    t ∈ B.occupiedChildTasks C := by sorry
