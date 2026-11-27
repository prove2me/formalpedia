-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxSourceWalk_eq_of_height_zero
-- name    : TreeStack.OrientedBranch.auxSourceWalk_eq_of_height_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:14:43.972955+00:00
-- url     : https://prove2.me/theorems/891c231f-4ba2-4278-b703-43138c9bf869
-- title:
--   Oriented Branch: aux Source Walk eq of height zero
-- statement:
--   One-step equation for the canonical source walk at height zero.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L106-L113
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L106-L113

import Mathlib
import Definitions.Def_TreeStack_LeafSlack
import Definitions.Def_TreeStack_HeightSource
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxSourceWalk_eq_of_height_zero
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hZero : auxHeight C ambientRoot hScores v = 0) :
    auxSourceWalk C ambientRoot hScores v =
      ⟨v, SimpleGraph.Walk.nil⟩ := by sorry
