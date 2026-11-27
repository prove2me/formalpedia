-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_occupiedChildTasks_nodup
-- name    : TreeStack.OrientedBranch.occupiedChildTasks_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:32:58.314814+00:00
-- url     : https://prove2.me/theorems/72e1e832-4c05-5aaa-8bdc-24b6f5801b7e
-- title:
--   Oriented Branch: occupied Child Tasks nodup
-- statement:
--   The Oriented Branch construction uses the occupied Child Tasks nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L906-L910
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L906-L910

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

theorem TreeStack.OrientedBranch.occupiedChildTasks_nodup
    (B : OrientedBranch T) (C : Configuration V) :
    (B.occupiedChildTasks C).Nodup := by sorry
