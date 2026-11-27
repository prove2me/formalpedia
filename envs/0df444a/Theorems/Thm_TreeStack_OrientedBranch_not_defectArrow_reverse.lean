-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_not_defectArrow_reverse
-- name    : TreeStack.OrientedBranch.not_defectArrow_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:53:22.8888+00:00
-- url     : https://prove2.me/theorems/a7a8490b-f8a2-4a67-9ffc-202dda1cc9b2
-- title:
--   Oriented Branch: not defect Arrow reverse
-- statement:
--   Forced orientations on retained support edges are antisymmetric.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L279-L287
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L279-L287

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.not_defectArrow_reverse
    (C : Configuration V) (B : OrientedBranch T)
    (hArrow : B.DefectArrow C)
    (hScores : ∀ v, score T C v ≤ 0) :
    ¬ B.reverseBranch.DefectArrow C := by sorry
