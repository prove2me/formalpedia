-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_edgeContribution_le_endpoint_add_separated_charge
-- name    : TreeStack.OrientedBranch.edgeContribution_le_endpoint_add_separated_charge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:14:15.252036+00:00
-- url     : https://prove2.me/theorems/64b6ded8-5da8-495b-a019-d98597ba349e
-- title:
--   Oriented Branch: edge Contribution le endpoint add separated charge
-- statement:
--   The uniform local edge inequality, packaged on the fixed finite edge
--   index while preserving the separation between retained defect charging and
--   literal-`EMPTY` boundary cancellation.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L179-L190
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L179-L190

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.edgeContribution_le_endpoint_add_separated_charge
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0)
    (e : T.graph.edgeFinset) :
    auxEdgeContribution C ambientRoot hScores (edgeBranch e) ≤
      auxWeightInt C ambientRoot hScores (edgeBranch e).root +
        auxWeightInt C ambientRoot hScores (edgeBranch e).parent +
        edgeSeparatedCharge C ambientRoot hScores e := by sorry
