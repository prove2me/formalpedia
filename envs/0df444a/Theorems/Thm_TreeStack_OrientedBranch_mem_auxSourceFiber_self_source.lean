-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_mem_auxSourceFiber_self_source
-- name    : TreeStack.OrientedBranch.mem_auxSourceFiber_self_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:30:36.295169+00:00
-- url     : https://prove2.me/theorems/be7400d2-ce4e-4deb-a27f-94d106c8166d
-- title:
--   Oriented Branch: mem aux Source Fiber self source
-- statement:
--   Every vertex belongs to the fibre indexed by its canonical source.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L28-L33
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L28-L33

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.mem_auxSourceFiber_self_source
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) :
    v ∈ auxSourceFiber C ambientRoot hScores
      (auxSource C ambientRoot hScores v) := by sorry
