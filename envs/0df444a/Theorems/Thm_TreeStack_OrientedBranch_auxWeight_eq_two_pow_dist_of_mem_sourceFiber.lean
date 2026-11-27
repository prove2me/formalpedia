-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxWeight_eq_two_pow_dist_of_mem_sourceFiber
-- name    : TreeStack.OrientedBranch.auxWeight_eq_two_pow_dist_of_mem_sourceFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:39.516932+00:00
-- url     : https://prove2.me/theorems/dea5220a-afa5-56b5-a0a8-0763d9075e35
-- title:
--   Oriented Branch: aux Weight eq two pow dist of mem source Fiber
-- statement:
--   On a source fibre, the auxiliary weight is exactly the power of two of
--   ambient-tree distance from that fibre's height-zero source.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L690-L699
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L690-L699

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxWeight_eq_two_pow_dist_of_mem_sourceFiber
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r v : V)
    (hv : v ∈ auxSourceFiber C ambientRoot hScores r) :
    auxWeight C ambientRoot hScores v =
      2 ^ T.graph.dist r v := by sorry
