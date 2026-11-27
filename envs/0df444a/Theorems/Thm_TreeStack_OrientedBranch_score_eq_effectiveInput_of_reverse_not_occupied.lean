-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_score_eq_effectiveInput_of_reverse_not_occupied
-- name    : TreeStack.OrientedBranch.score_eq_effectiveInput_of_reverse_not_occupied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:01:23.637996+00:00
-- url     : https://prove2.me/theorems/eb680786-07e3-5883-b1c6-f906c306f45b
-- title:
--   Oriented Branch: score eq effective Input of reverse not occupied
-- statement:
--   If the exterior side of an oriented edge is empty, its message remains
--   literally `EMPTY`, and therefore contributes zero to the rooted score.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L230-L236
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L230-L236

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.score_eq_effectiveInput_of_reverse_not_occupied
    (C : Configuration V) (B : OrientedBranch T)
    (hEmpty : ¬ B.reverseBranch.Occupied C) :
    score T C B.root = B.effectiveInput C := by sorry
