-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_nondefectiveSupportEdge_auxEdgeContribution_le_baseline
-- name    : TreeStack.OrientedBranch.nondefectiveSupportEdge_auxEdgeContribution_le_baseline
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:09:08.515594+00:00
-- url     : https://prove2.me/theorems/b705f2d0-7d59-5c3c-8a97-71057fc692fe
-- title:
--   Oriented Branch: nondefective Support Edge aux Edge Contribution le baseline
-- statement:
--   A retained edge with no positive defect excess contributes at most its two
--   endpoint weights.  Oriented zero-excess states still use their forced
--   auxiliary direction, which is why every `DefectArrow` participates in
--   `AuxArrow`, not only defective ones.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L242-L297
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean#L242-L297

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
import Definitions.Def_TreeStack_AuxiliaryCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.nondefectiveSupportEdge_auxEdgeContribution_le_baseline
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hEdge : B.SupportEdge C)
    (hNondef : ¬ B.DefectiveSupportEdge C) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent := by sorry
