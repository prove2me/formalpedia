-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_configurationSlackTerm_nonneg
-- name    : TreeStack.OrientedBranch.configurationSlackTerm_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:17:54.263446+00:00
-- url     : https://prove2.me/theorems/8a649946-bc8e-42aa-89a0-fb9c7bb3f441
-- title:
--   Oriented Branch: configuration Slack Term nonneg
-- statement:
--   Every configuration-slack summand is nonnegative.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L117-L124
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L117-L124

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.configurationSlackTerm_nonneg
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) :
    0 ≤
      (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ) := by sorry
