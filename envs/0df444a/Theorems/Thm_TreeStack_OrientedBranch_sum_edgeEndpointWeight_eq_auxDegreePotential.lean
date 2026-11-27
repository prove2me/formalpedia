-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_sum_edgeEndpointWeight_eq_auxDegreePotential
-- name    : TreeStack.OrientedBranch.sum_edgeEndpointWeight_eq_auxDegreePotential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:16:36.746929+00:00
-- url     : https://prove2.me/theorems/d1306827-b175-425c-b119-7664579e5258
-- title:
--   Oriented Branch: sum edge Endpoint Weight eq aux Degree Potential
-- statement:
--   Sum of the two endpoint weights over undirected edges equals the weighted
--   degree potential.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L392-L431
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L392-L431

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.sum_edgeEndpointWeight_eq_auxDegreePotential
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ e : T.graph.edgeFinset,
      (auxWeightInt C ambientRoot hScores (edgeBranch e).root +
        auxWeightInt C ambientRoot hScores (edgeBranch e).parent)) =
      auxDegreePotential C ambientRoot hScores := by sorry
