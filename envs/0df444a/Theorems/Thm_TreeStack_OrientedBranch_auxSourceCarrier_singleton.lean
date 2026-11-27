-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxSourceCarrier_singleton
-- name    : TreeStack.OrientedBranch.auxSourceCarrier_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:10.177086+00:00
-- url     : https://prove2.me/theorems/4e84c84e-19db-52bb-b11b-0a3dbff93784
-- title:
--   Oriented Branch: aux Source Carrier singleton
-- statement:
--   A singleton source carrier is exactly its source fibre.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L388-L395
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L388-L395

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxSourceCarrier_singleton
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r : V) :
    auxSourceCarrier C ambientRoot hScores {r} =
      auxSourceFiber C ambientRoot hScores r := by sorry
