-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxSource_height_zero
-- name    : TreeStack.OrientedBranch.auxSource_height_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:33.73966+00:00
-- url     : https://prove2.me/theorems/226d653b-8623-500d-ba35-326755b598ef
-- title:
--   Oriented Branch: aux Source height zero
-- statement:
--   Every canonical source really has auxiliary height zero.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L292-L315
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L292-L315

import Mathlib
import Definitions.Def_TreeStack_LeafSlack
import Definitions.Def_TreeStack_HeightSource
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxSource_height_zero
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    auxHeight C ambientRoot hScores
      (auxSource C ambientRoot hScores v) = 0 := by sorry
