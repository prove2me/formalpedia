-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_two_mul_auxWeightInt_le_of_auxArrow
-- name    : TreeStack.OrientedBranch.two_mul_auxWeightInt_le_of_auxArrow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:06:58.1538+00:00
-- url     : https://prove2.me/theorems/e73bc742-707c-4856-85b8-4c61ca9ceae5
-- title:
--   Oriented Branch: two mul aux Weight Int le of aux Arrow
-- statement:
--   Integer doubling form used directly by `DefectCharge.lean`.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L489-L501
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L489-L501

import Mathlib
import Definitions.Def_TreeStack_DefectCharge
import Definitions.Def_TreeStack_Auxiliary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.two_mul_auxWeightInt_le_of_auxArrow
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    2 * auxWeightInt C ambientRoot hScores u ≤
      auxWeightInt C ambientRoot hScores v := by sorry
