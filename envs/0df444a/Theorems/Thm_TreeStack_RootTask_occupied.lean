-- Prove2me | Theorems.Thm_TreeStack_RootTask_occupied
-- name    : TreeStack.RootTask.occupied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:58.825168+00:00
-- url     : https://prove2.me/theorems/efd707a4-ab58-5873-a4d6-7df2e95cf807
-- title:
--   Root Task: occupied
-- statement:
--   The Root Task construction uses the occupied property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L196-L200
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L196-L200

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_occupied

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.RootTask.occupied
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) :
    t.branch.Occupied C := by sorry
