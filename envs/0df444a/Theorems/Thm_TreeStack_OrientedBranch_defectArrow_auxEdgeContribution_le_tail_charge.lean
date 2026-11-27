-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_defectArrow_auxEdgeContribution_le_tail_charge
-- name    : TreeStack.OrientedBranch.defectArrow_auxEdgeContribution_le_tail_charge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:08:55.713747+00:00
-- url     : https://prove2.me/theorems/7847096e-3d1e-4676-8eb8-1cf395dc8135
-- title:
--   Oriented Branch: defect Arrow aux Edge Contribution le tail charge
-- statement:
--   A defective forced arrow has its weighted edge excess payable by its tail
--   defect.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L37-L77
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L37-L77

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
import Definitions.Def_TreeStack_AuxiliaryCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.defectArrow_auxEdgeContribution_le_tail_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hDef : B.DefectiveSupportEdge C)
    (hArrow : B.DefectArrow C) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        auxWeightInt C ambientRoot hScores B.root *
          scoreDefect T C B.root := by sorry
