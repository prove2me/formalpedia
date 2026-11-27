-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxSourceWalk_isPath
-- name    : TreeStack.OrientedBranch.auxSourceWalk_isPath
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:26.905962+00:00
-- url     : https://prove2.me/theorems/8d4ffb5e-ee50-5da2-9519-712225eb3961
-- title:
--   Oriented Branch: aux Source Walk is Path
-- statement:
--   The canonical source walk is simple because height strictly decreases
--   backwards along it.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L185-L216
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/HeightSource.lean#L185-L216

import Mathlib
import Definitions.Def_TreeStack_LeafSlack
import Definitions.Def_TreeStack_HeightSource
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxSourceWalk_isPath
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    (auxSourceWalk C ambientRoot hScores v).2.IsPath := by sorry
