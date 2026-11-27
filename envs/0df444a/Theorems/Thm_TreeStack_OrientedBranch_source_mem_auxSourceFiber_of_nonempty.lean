-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_source_mem_auxSourceFiber_of_nonempty
-- name    : TreeStack.OrientedBranch.source_mem_auxSourceFiber_of_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:48.007079+00:00
-- url     : https://prove2.me/theorems/4bb57b7e-cc75-4418-9bba-7862cdd645eb
-- title:
--   Oriented Branch: source mem aux Source Fiber of nonempty
-- statement:
--   The index of every nonempty source fibre belongs to that fibre.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L646-L656
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L646-L656

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.source_mem_auxSourceFiber_of_nonempty
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r : V}
    (hNonempty : (auxSourceFiber C ambientRoot hScores r).Nonempty) :
    r ∈ auxSourceFiber C ambientRoot hScores r := by sorry
