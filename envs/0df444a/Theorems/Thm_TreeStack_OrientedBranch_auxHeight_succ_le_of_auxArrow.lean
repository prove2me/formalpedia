-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxHeight_succ_le_of_auxArrow
-- name    : TreeStack.OrientedBranch.auxHeight_succ_le_of_auxArrow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:08:26.401924+00:00
-- url     : https://prove2.me/theorems/d38acf43-08ad-4870-b881-02a2426a2d76
-- title:
--   Oriented Branch: aux Height succ le of aux Arrow
-- statement:
--   Every auxiliary arrow extends a longest directed path by one step.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L400-L416
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L400-L416

import Mathlib
import Definitions.Def_TreeStack_DefectCharge
import Definitions.Def_TreeStack_Auxiliary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxHeight_succ_le_of_auxArrow
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    auxHeight C ambientRoot hScores u + 1 ≤
      auxHeight C ambientRoot hScores v := by sorry
