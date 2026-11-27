-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxWeightInt_nonneg
-- name    : TreeStack.OrientedBranch.auxWeightInt_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:06:52.486131+00:00
-- url     : https://prove2.me/theorems/3877c9d5-e48c-5865-81c4-ff2284ebdaae
-- title:
--   Oriented Branch: aux Weight Int nonneg
-- statement:
--   Integer auxiliary weights are nonnegative.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L470-L475
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L470-L475

import Mathlib
import Definitions.Def_TreeStack_DefectCharge
import Definitions.Def_TreeStack_Auxiliary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxWeightInt_nonneg
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    0 ≤ auxWeightInt C ambientRoot hScores v := by sorry
