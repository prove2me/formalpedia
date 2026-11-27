-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxDegreePotential_eq_leaf_add_internal
-- name    : TreeStack.OrientedBranch.auxDegreePotential_eq_leaf_add_internal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:37.789089+00:00
-- url     : https://prove2.me/theorems/f0df31c2-9936-58ba-9fb6-29bd89aaea37
-- title:
--   Oriented Branch: aux Degree Potential eq leaf add internal
-- statement:
--   Split the weighted degree potential into leaf and internal terms.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L244-L291
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L244-L291

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxDegreePotential_eq_leaf_add_internal [Nontrivial V]
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxDegreePotential C ambientRoot hScores =
      (∑ v ∈ ambientLeaves (T := T),
        auxWeightInt C ambientRoot hScores v) +
      auxInternalDegreePotential C ambientRoot hScores := by sorry
