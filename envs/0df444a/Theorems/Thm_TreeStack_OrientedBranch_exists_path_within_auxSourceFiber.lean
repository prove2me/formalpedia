-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_exists_path_within_auxSourceFiber
-- name    : TreeStack.OrientedBranch.exists_path_within_auxSourceFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:15:45.80181+00:00
-- url     : https://prove2.me/theorems/b4c59d3e-bb83-5c97-aab4-304e8ccd9470
-- title:
--   Oriented Branch: exists path within aux Source Fiber
-- statement:
--   A source fibre is path-connected by a simple ambient-tree path whose
--   support remains entirely inside the fibre.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L119-L135
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L119-L135

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.exists_path_within_auxSourceFiber
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r x y : V)
    (hx : x ∈ auxSourceFiber C ambientRoot hScores r)
    (hy : y ∈ auxSourceFiber C ambientRoot hScores r) :
    ∃ p : T.graph.Walk x y,
      p.IsPath ∧
        ∀ z ∈ p.support,
          z ∈ auxSourceFiber C ambientRoot hScores r := by sorry
