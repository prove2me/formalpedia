-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_edgeSeparatedCharge_le_owner_charge
-- name    : TreeStack.OrientedBranch.edgeSeparatedCharge_le_owner_charge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:13:56.711058+00:00
-- url     : https://prove2.me/theorems/ed0e533a-844f-4903-8617-7bd073cbb652
-- title:
--   Oriented Branch: edge Separated Charge le owner charge
-- statement:
--   A separated edge charge never exceeds the single rooted-owner defect
--   budget assigned to that ambient edge.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L130-L154
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L130-L154

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.edgeSeparatedCharge_le_owner_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (e : T.graph.edgeFinset) :
    edgeSeparatedCharge C ambientRoot hScores e ≤
      auxWeightInt C ambientRoot hScores (edgeOwner ambientRoot e) *
        scoreDefect T C (edgeOwner ambientRoot e) := by sorry
