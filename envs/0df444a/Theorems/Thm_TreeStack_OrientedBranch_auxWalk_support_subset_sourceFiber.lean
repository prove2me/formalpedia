-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxWalk_support_subset_sourceFiber
-- name    : TreeStack.OrientedBranch.auxWalk_support_subset_sourceFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:56.532127+00:00
-- url     : https://prove2.me/theorems/f7c35cf9-c700-44fb-b3f4-8459de88a281
-- title:
--   Oriented Branch: aux Walk support subset source Fiber
-- statement:
--   The canonical walk from a vertex stays entirely in its source fibre.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L53-L63
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L53-L63

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxWalk_support_subset_sourceFiber
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) :
    ∀ x ∈ (auxWalk C ambientRoot hScores v).support,
      x ∈ auxSourceFiber C ambientRoot hScores
        (auxSource C ambientRoot hScores v) := by sorry
