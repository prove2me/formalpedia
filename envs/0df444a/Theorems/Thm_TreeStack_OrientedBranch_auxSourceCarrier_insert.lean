-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxSourceCarrier_insert
-- name    : TreeStack.OrientedBranch.auxSourceCarrier_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:02.922908+00:00
-- url     : https://prove2.me/theorems/cd379712-3461-58d4-bc86-b8b12448bea6
-- title:
--   Oriented Branch: aux Source Carrier insert
-- statement:
--   Inserting one source adds exactly its whole canonical fibre.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L377-L385
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L377-L385

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxSourceCarrier_insert
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (R : Finset V) (r : V) :
    auxSourceCarrier C ambientRoot hScores (insert r R) =
      auxSourceCarrier C ambientRoot hScores R ∪
        auxSourceFiber C ambientRoot hScores r := by sorry
