-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_mem_auxSourceCarrier
-- name    : TreeStack.OrientedBranch.mem_auxSourceCarrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:15:40.155923+00:00
-- url     : https://prove2.me/theorems/1bb9723a-8a9b-4c97-8f20-cae390cd5477
-- title:
--   Oriented Branch: mem aux Source Carrier
-- statement:
--   The Oriented Branch construction uses the mem aux Source Carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L368-L374
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L368-L374

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.mem_auxSourceCarrier
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (R : Finset V) (v : V) :
    v ∈ auxSourceCarrier C ambientRoot hScores R ↔
      auxSource C ambientRoot hScores v ∈ R := by sorry
