-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxSourceWalk_support_height_le
-- name    : TreeStack.OrientedBranch.auxSourceWalk_support_height_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:38.558108+00:00
-- url     : https://prove2.me/theorems/2c57f316-18ab-40aa-87ce-09ca0acb1c5a
-- title:
--   Oriented Branch: aux Source Walk support height le
-- statement:
--   Every vertex occurring on the canonical source walk has height at most the
--   height of the starting vertex.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L148-L181
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L148-L181

import Mathlib
import Definitions.Def_TreeStack_LeafSlack
import Definitions.Def_TreeStack_HeightSource
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxSourceWalk_support_height_le
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v x : V)
    (hx : x ∈ (auxSourceWalk C ambientRoot hScores v).2.support) :
    auxHeight C ambientRoot hScores x ≤
      auxHeight C ambientRoot hScores v := by sorry
