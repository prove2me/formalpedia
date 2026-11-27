-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxWeightedMass_sub_configurationSlack_eq_mass
-- name    : TreeStack.OrientedBranch.auxWeightedMass_sub_configurationSlack_eq_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:07.651627+00:00
-- url     : https://prove2.me/theorems/ff122b65-31f2-42e3-bc0c-ec9896633bb9
-- title:
--   Oriented Branch: aux Weighted Mass sub configuration Slack eq mass
-- statement:
--   The exact conversion identity from weighted mass to ordinary mass.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L127-L144
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L127-L144

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxWeightedMass_sub_configurationSlack_eq_mass
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxWeightedMass C ambientRoot hScores -
        auxConfigurationSlack C ambientRoot hScores =
      (mass C : ℤ) := by sorry
