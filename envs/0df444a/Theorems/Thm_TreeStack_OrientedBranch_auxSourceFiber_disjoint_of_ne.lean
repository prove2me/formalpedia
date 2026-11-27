-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxSourceFiber_disjoint_of_ne
-- name    : TreeStack.OrientedBranch.auxSourceFiber_disjoint_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:23.154416+00:00
-- url     : https://prove2.me/theorems/15a3e221-3e94-527b-afba-c29449be71f5
-- title:
--   Oriented Branch: aux Source Fiber disjoint of ne
-- statement:
--   Distinct canonical sources have disjoint fibres.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L102-L115
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L102-L115

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxSourceFiber_disjoint_of_ne
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r s : V} (hrs : r ≠ s) :
    Disjoint
      (auxSourceFiber C ambientRoot hScores r)
      (auxSourceFiber C ambientRoot hScores s) := by sorry
