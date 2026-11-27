-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_leaf_pos_of_auxWeightInt_ne_one
-- name    : TreeStack.OrientedBranch.leaf_pos_of_auxWeightInt_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:17:33.23523+00:00
-- url     : https://prove2.me/theorems/1985adc9-ac67-4924-98f4-aeab5c514335
-- title:
--   Oriented Branch: leaf pos of aux Weight Int ne one
-- statement:
--   If an ambient leaf has non-unit auxiliary weight, then it is occupied.
--   Positive height supplies an incoming auxiliary arrow; that arrow is retained,
--   and the leaf-side deleted-edge branch is the singleton leaf.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L53-L88
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L53-L88

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.leaf_pos_of_auxWeightInt_ne_one
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V)
    (hLeaf : T.graph.degree v = 1)
    (hWeight : auxWeightInt C ambientRoot hScores v ≠ 1) :
    0 < C v := by sorry
