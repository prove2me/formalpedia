-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_defectArrow_auxEdgeContribution_le_baseline_of_head_defect_zero
-- name    : TreeStack.OrientedBranch.defectArrow_auxEdgeContribution_le_baseline_of_head_defect_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:09:01.618597+00:00
-- url     : https://prove2.me/theorems/941ab515-eede-52f0-8a06-4dc02cc0f071
-- title:
--   Oriented Branch: defect Arrow aux Edge Contribution le baseline of head defect zero
-- statement:
--   A forced oriented edge with zero head defect has no positive excess over
--   the endpoint baseline.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L204-L236
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L204-L236

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
import Definitions.Def_TreeStack_AuxiliaryCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.defectArrow_auxEdgeContribution_le_baseline_of_head_defect_zero
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hArrow : B.DefectArrow C)
    (hDeltaZero : scoreDefect T C B.parent = 0) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent := by sorry
