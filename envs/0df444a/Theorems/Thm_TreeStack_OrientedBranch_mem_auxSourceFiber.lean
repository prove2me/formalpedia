-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_mem_auxSourceFiber
-- name    : TreeStack.OrientedBranch.mem_auxSourceFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:15:46.148674+00:00
-- url     : https://prove2.me/theorems/fe26f96a-c469-478b-bb0a-640936007a7d
-- title:
--   Oriented Branch: mem aux Source Fiber
-- statement:
--   The Oriented Branch construction uses the mem aux Source Fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L20-L25
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L20-L25

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.mem_auxSourceFiber
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (r v : V) :
    v ∈ auxSourceFiber C ambientRoot hScores r ↔
      auxSource C ambientRoot hScores v = r := by sorry
