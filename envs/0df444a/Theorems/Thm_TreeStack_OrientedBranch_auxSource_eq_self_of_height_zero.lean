-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxSource_eq_self_of_height_zero
-- name    : TreeStack.OrientedBranch.auxSource_eq_self_of_height_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:15:13.953071+00:00
-- url     : https://prove2.me/theorems/86ce6979-35d8-4e7b-9d86-846e5fa678aa
-- title:
--   Oriented Branch: aux Source eq self of height zero
-- statement:
--   A zero-height vertex is its own canonical source.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L271-L277
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L271-L277

import Mathlib
import Definitions.Def_TreeStack_LeafSlack
import Definitions.Def_TreeStack_HeightSource
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxSource_eq_self_of_height_zero
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hZero : auxHeight C ambientRoot hScores v = 0) :
    auxSource C ambientRoot hScores v = v := by sorry
