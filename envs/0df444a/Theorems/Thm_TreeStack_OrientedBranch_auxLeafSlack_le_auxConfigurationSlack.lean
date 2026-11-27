-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxLeafSlack_le_auxConfigurationSlack
-- name    : TreeStack.OrientedBranch.auxLeafSlack_le_auxConfigurationSlack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:06.104742+00:00
-- url     : https://prove2.me/theorems/105ee170-3a69-516f-923d-d6e9ce81a8a8
-- title:
--   Oriented Branch: aux Leaf Slack le aux Configuration Slack
-- statement:
--   Occupied ambient leaves pay all of the leaf-weight slack.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L147-L169
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L147-L169

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxLeafSlack_le_auxConfigurationSlack
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxLeafSlack C ambientRoot hScores ≤
      auxConfigurationSlack C ambientRoot hScores := by sorry
