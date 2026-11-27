-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_sum_auxEdgeContribution_le_degree_add_defect
-- name    : TreeStack.OrientedBranch.sum_auxEdgeContribution_le_degree_add_defect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:17:32.195524+00:00
-- url     : https://prove2.me/theorems/4c7b3955-d79e-4f27-93ef-28ebd469ff7c
-- title:
--   Oriented Branch: sum aux Edge Contribution le degree add defect
-- statement:
--   Global sum of the local edge inequalities with retained-defect and
--   literal-`EMPTY` cancellation kept distinct until after summation.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L437-L459
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L437-L459

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
set_option maxHeartbeats 800000

theorem TreeStack.OrientedBranch.sum_auxEdgeContribution_le_degree_add_defect
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ e : T.graph.edgeFinset,
      auxEdgeContribution C ambientRoot hScores (edgeBranch e)) ≤
      auxDegreePotential C ambientRoot hScores +
        auxDefectBudget C ambientRoot hScores := by sorry
