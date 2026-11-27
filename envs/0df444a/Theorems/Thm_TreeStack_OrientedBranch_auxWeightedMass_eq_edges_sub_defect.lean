-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxWeightedMass_eq_edges_sub_defect
-- name    : TreeStack.OrientedBranch.auxWeightedMass_eq_edges_sub_defect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:16:09.564342+00:00
-- url     : https://prove2.me/theorems/1fa05738-68bd-454c-a1f8-dea9b9324f0a
-- title:
--   Oriented Branch: aux Weighted Mass eq edges sub defect
-- statement:
--   Exact weighted score expansion: weighted mass is the edge contribution
--   sum minus the total weighted defect budget.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L377-L388
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L377-L388

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxWeightedMass_eq_edges_sub_defect
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxWeightedMass C ambientRoot hScores =
      (∑ e : T.graph.edgeFinset,
        auxEdgeContribution C ambientRoot hScores (edgeBranch e)) -
        auxDefectBudget C ambientRoot hScores := by sorry
