-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxWeightInt_le_two_pow_dist
-- name    : TreeStack.OrientedBranch.auxWeightInt_le_two_pow_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:53.021519+00:00
-- url     : https://prove2.me/theorems/5718d089-4afc-5f2e-8921-401ba53996a6
-- title:
--   Oriented Branch: aux Weight Int le two pow dist
-- statement:
--   A pointwise domination of auxiliary height by distance from one root gives
--   the corresponding powers-of-two domination in the integer weights.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/UpperBound.lean#L14-L26
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/UpperBound.lean#L14-L26

import Mathlib
import Definitions.Def_TreeStack_Consolidation
import Definitions.Def_TreeStack_UpperBound
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxWeightInt_le_two_pow_dist
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r v : V)
    (hHeight :
      auxHeight C ambientRoot hScores v ≤ T.graph.dist r v) :
    auxWeightInt C ambientRoot hScores v ≤
      ((2 ^ T.graph.dist r v : ℕ) : ℤ) := by sorry
