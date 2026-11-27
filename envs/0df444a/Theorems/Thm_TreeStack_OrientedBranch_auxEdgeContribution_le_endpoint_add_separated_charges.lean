-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxEdgeContribution_le_endpoint_add_separated_charges
-- name    : TreeStack.OrientedBranch.auxEdgeContribution_le_endpoint_add_separated_charges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:09:58.291268+00:00
-- url     : https://prove2.me/theorems/def9710a-1869-4479-af77-17a6b21af114
-- title:
--   Oriented Branch: aux Edge Contribution le endpoint add separated charges
-- statement:
--   Uniform ambient-edge estimate with the two cancellation mechanisms kept
--   separate: only genuinely defective retained edges receive owner-paid defect
--   charge, while nonretained edges use their distinct `EMPTY`-boundary term.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L442-L505
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L442-L505

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
import Definitions.Def_TreeStack_AuxiliaryCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxEdgeContribution_le_endpoint_add_separated_charges
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        retainedDefectCharge C ambientRoot hScores B +
        emptyBoundaryCharge C ambientRoot hScores B := by sorry
