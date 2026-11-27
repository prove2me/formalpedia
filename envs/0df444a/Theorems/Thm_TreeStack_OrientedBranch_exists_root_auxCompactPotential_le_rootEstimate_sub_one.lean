-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_exists_root_auxCompactPotential_le_rootEstimate_sub_one
-- name    : TreeStack.OrientedBranch.exists_root_auxCompactPotential_le_rootEstimate_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:30.788996+00:00
-- url     : https://prove2.me/theorems/d5b789be-eab1-4714-adf4-7370e03d82d8
-- title:
--   Oriented Branch: exists root aux Compact Potential le root Estimate sub one
-- statement:
--   Consolidation turns the compact auxiliary potential into one rooted
--   Csernák--Soukup estimator, with the leading one removed.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/UpperBound.lean#L57-L75
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/UpperBound.lean#L57-L75

import Mathlib
import Definitions.Def_TreeStack_Consolidation
import Definitions.Def_TreeStack_UpperBound
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.exists_root_auxCompactPotential_le_rootEstimate_sub_one
    [Nontrivial V]
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    ∃ r : V,
      auxCompactPotential C ambientRoot hScores ≤
        (rootEstimate T r : ℤ) - 1 := by sorry
