-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_defectArrow_auxEdgeContribution_le_head_charge
-- name    : TreeStack.OrientedBranch.defectArrow_auxEdgeContribution_le_head_charge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:10:48.786637+00:00
-- url     : https://prove2.me/theorems/3ab05cf9-0d42-4223-90d5-2341e2583d6e
-- title:
--   Oriented Branch: defect Arrow aux Edge Contribution le head charge
-- statement:
--   The same defective forced-arrow excess can instead be paid by its head
--   defect, using the auxiliary doubling inequality.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L81-L121
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L81-L121

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
import Definitions.Def_TreeStack_AuxiliaryCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.defectArrow_auxEdgeContribution_le_head_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hDef : B.DefectiveSupportEdge C)
    (hArrow : B.DefectArrow C) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        auxWeightInt C ambientRoot hScores B.parent *
          scoreDefect T C B.parent := by sorry
