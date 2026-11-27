-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_supportEdge_defectArrow_or_reverse_or_both_neg
-- name    : TreeStack.OrientedBranch.supportEdge_defectArrow_or_reverse_or_both_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:50:30.163178+00:00
-- url     : https://prove2.me/theorems/06928a33-7088-5195-8480-98e8cecedf92
-- title:
--   Oriented Branch: support Edge defect Arrow or reverse or both neg
-- statement:
--   Every retained support edge has either a nonnegative message in one
--   orientation or two negative messages.  Together with
--   `not_defectArrow_reverse`, all-nonpositive scores make the nonnegative
--   orientation unique when it exists.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L309-L330
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L309-L330

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.supportEdge_defectArrow_or_reverse_or_both_neg
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) :
    B.DefectArrow C ∨
      B.reverseBranch.DefectArrow C ∨
        (messageContribution (branchMessage C B) < 0 ∧
          messageContribution (branchMessage C B.reverseBranch) < 0) := by sorry
