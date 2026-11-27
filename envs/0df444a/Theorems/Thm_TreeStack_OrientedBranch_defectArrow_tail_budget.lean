-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_defectArrow_tail_budget
-- name    : TreeStack.OrientedBranch.defectArrow_tail_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:53:15.488005+00:00
-- url     : https://prove2.me/theorems/dd12e471-c4d2-46a1-941f-4e0bdb320d2f
-- title:
--   Oriented Branch: defect Arrow tail budget
-- statement:
--   The tail of a forced defect arrow has enough endpoint-defect budget to pay
--   twice the head defect.  This is the concrete support-core form of the local
--   oriented-edge budget inequality.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L292-L303
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L292-L303

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.defectArrow_tail_budget
    (C : Configuration V) (B : OrientedBranch T)
    (hArrow : B.DefectArrow C)
    (hScores : ∀ v, score T C v ≤ 0) :
    2 * scoreDefect T C B.parent ≤ scoreDefect T C B.root := by sorry
