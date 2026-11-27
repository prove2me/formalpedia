-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_one_le_auxWeightInt
-- name    : TreeStack.OrientedBranch.one_le_auxWeightInt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:13:42.184813+00:00
-- url     : https://prove2.me/theorems/37176b8a-6966-4952-89c6-72573fbcfad5
-- title:
--   Oriented Branch: one le aux Weight Int
-- statement:
--   Integer auxiliary weights are at least one.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L39-L48
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L39-L48

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.one_le_auxWeightInt
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) :
    1 ≤ auxWeightInt C ambientRoot hScores v := by sorry
