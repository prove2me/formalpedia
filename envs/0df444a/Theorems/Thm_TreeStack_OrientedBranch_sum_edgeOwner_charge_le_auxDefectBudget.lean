-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_sum_edgeOwner_charge_le_auxDefectBudget
-- name    : TreeStack.OrientedBranch.sum_edgeOwner_charge_le_auxDefectBudget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:13:38.887097+00:00
-- url     : https://prove2.me/theorems/4ca21b58-48f9-5e48-b9af-9115522d2013
-- title:
--   Oriented Branch: sum edge Owner charge le aux Defect Budget
-- statement:
--   The owner charges over all ambient edges fit inside the total vertex
--   defect budget, by injectivity of the rooted-owner assignment.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L86-L117
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L86-L117

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.sum_edgeOwner_charge_le_auxDefectBudget
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ e : T.graph.edgeFinset,
      auxWeightInt C ambientRoot hScores (edgeOwner ambientRoot e) *
        scoreDefect T C (edgeOwner ambientRoot e)) ≤
      auxDefectBudget C ambientRoot hScores := by sorry
