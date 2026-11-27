-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_two_mul_auxWeight_le_of_auxArrow
-- name    : TreeStack.OrientedBranch.two_mul_auxWeight_le_of_auxArrow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:08:17.386992+00:00
-- url     : https://prove2.me/theorems/c9afad70-eb75-43d8-8567-9d320558e2d4
-- title:
--   Oriented Branch: two mul aux Weight le of aux Arrow
-- statement:
--   The key doubling inequality: weights at least double along every auxiliary
--   directed edge.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L445-L459
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L445-L459

import Mathlib
import Definitions.Def_TreeStack_DefectCharge
import Definitions.Def_TreeStack_Auxiliary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.two_mul_auxWeight_le_of_auxArrow
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    2 * auxWeight C ambientRoot hScores u ≤
      auxWeight C ambientRoot hScores v := by sorry
