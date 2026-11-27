-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_sum_auxEdgeContribution_eq_neg_messages
-- name    : TreeStack.OrientedBranch.sum_auxEdgeContribution_eq_neg_messages
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:14:52.150799+00:00
-- url     : https://prove2.me/theorems/38b61a6f-892e-44b4-b5cc-ac5df84ed578
-- title:
--   Oriented Branch: sum aux Edge Contribution eq neg messages
-- statement:
--   The sum of undirected weighted edge contributions is the negative
--   weighted root-message sum.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L353-L373
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L353-L373

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.sum_auxEdgeContribution_eq_neg_messages
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ e : T.graph.edgeFinset,
      auxEdgeContribution C ambientRoot hScores (edgeBranch e)) =
      -(∑ v : V,
        auxWeightInt C ambientRoot hScores v * rootMessageSum T C v) := by sorry
