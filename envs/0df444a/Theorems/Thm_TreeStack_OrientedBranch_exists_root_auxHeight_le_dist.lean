-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_exists_root_auxHeight_le_dist
-- name    : TreeStack.OrientedBranch.exists_root_auxHeight_le_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:54.988507+00:00
-- url     : https://prove2.me/theorems/946019bf-0b23-4d03-80c3-1b5e679f0825
-- title:
--   Oriented Branch: exists root aux Height le dist
-- statement:
--   The canonical source partition therefore consolidates to one ambient root
--   whose distance profile dominates every auxiliary height.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L545-L576
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L545-L576

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.exists_root_auxHeight_le_dist
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    ∃ r : V, ∀ v : V,
      auxHeight C ambientRoot hScores v ≤ T.graph.dist r v := by sorry
