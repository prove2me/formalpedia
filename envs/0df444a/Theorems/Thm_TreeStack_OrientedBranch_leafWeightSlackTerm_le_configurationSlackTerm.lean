-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_leafWeightSlackTerm_le_configurationSlackTerm
-- name    : TreeStack.OrientedBranch.leafWeightSlackTerm_le_configurationSlackTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:02.105006+00:00
-- url     : https://prove2.me/theorems/d5b80728-0938-4f0a-b304-b96c365d2829
-- title:
--   Oriented Branch: leaf Weight Slack Term le configuration Slack Term
-- statement:
--   At an ambient leaf, the configuration-weight slack pays the entire excess
--   of the auxiliary leaf weight over one.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L92-L114
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L92-L114

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.leafWeightSlackTerm_le_configurationSlackTerm
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V)
    (hLeaf : T.graph.degree v = 1) :
    auxWeightInt C ambientRoot hScores v - 1 ≤
      (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ) := by sorry
