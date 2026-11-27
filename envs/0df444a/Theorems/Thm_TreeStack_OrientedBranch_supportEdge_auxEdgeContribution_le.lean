-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_supportEdge_auxEdgeContribution_le
-- name    : TreeStack.OrientedBranch.supportEdge_auxEdgeContribution_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:10:05.848578+00:00
-- url     : https://prove2.me/theorems/dab4045d-b968-4d32-8346-19ca21f02fc1
-- title:
--   Oriented Branch: support Edge aux Edge Contribution le
-- statement:
--   Uniform retained-edge estimate, exposing a charge exactly when the edge is
--   defective.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L346-L366
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L346-L366

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
import Definitions.Def_TreeStack_AuxiliaryCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.supportEdge_auxEdgeContribution_le
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        if B.DefectiveSupportEdge C then
          auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
            scoreDefect T C (B.rootedOwner ambientRoot)
        else 0 := by sorry
