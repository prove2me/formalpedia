-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxWeightInt_eq_one_of_not_occupied
-- name    : TreeStack.OrientedBranch.auxWeightInt_eq_one_of_not_occupied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:08:36.915556+00:00
-- url     : https://prove2.me/theorems/bada9d28-cb92-433d-9a80-dc71ccdd8572
-- title:
--   Oriented Branch: aux Weight Int eq one of not occupied
-- statement:
--   The root of an empty branch has unit auxiliary weight.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L478-L486
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L478-L486

import Mathlib
import Definitions.Def_TreeStack_DefectCharge
import Definitions.Def_TreeStack_Auxiliary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxWeightInt_eq_one_of_not_occupied
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) (hEmpty : ¬ B.Occupied C) :
    auxWeightInt C ambientRoot hScores B.root = 1 := by sorry
