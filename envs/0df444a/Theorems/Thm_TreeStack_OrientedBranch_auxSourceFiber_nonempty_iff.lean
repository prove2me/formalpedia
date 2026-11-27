-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxSourceFiber_nonempty_iff
-- name    : TreeStack.OrientedBranch.auxSourceFiber_nonempty_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:16:31.15415+00:00
-- url     : https://prove2.me/theorems/28a68e01-5183-4a0a-b87f-b09832909dba
-- title:
--   Oriented Branch: aux Source Fiber nonempty iff
-- statement:
--   A source fibre is nonempty exactly when its index is itself a canonical
--   height-zero source.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L37-L50
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L37-L50

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxSourceFiber_nonempty_iff
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (r : V) :
    (auxSourceFiber C ambientRoot hScores r).Nonempty ↔
      auxHeight C ambientRoot hScores r = 0 := by sorry
