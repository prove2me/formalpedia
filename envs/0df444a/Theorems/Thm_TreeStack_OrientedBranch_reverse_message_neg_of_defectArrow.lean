-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_reverse_message_neg_of_defectArrow
-- name    : TreeStack.OrientedBranch.reverse_message_neg_of_defectArrow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:53:09.417021+00:00
-- url     : https://prove2.me/theorems/f64dbf57-1889-409f-99cc-838065a98918
-- title:
--   Oriented Branch: reverse message neg of defect Arrow
-- statement:
--   A forced defect arrow has a strictly negative reverse message under
--   all-nonpositive rooted scores.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L262-L276
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L262-L276

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.reverse_message_neg_of_defectArrow
    (C : Configuration V) (B : OrientedBranch T)
    (hArrow : B.DefectArrow C)
    (hScores : ∀ v, score T C v ≤ 0) :
    messageContribution (branchMessage C B.reverseBranch) < 0 := by sorry
