-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxSourceCarrier_disjoint_fiber_of_not_mem
-- name    : TreeStack.OrientedBranch.auxSourceCarrier_disjoint_fiber_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:02.683943+00:00
-- url     : https://prove2.me/theorems/3bc1d457-b7a7-5144-b736-aec50030d46e
-- title:
--   Oriented Branch: aux Source Carrier disjoint fiber of not mem
-- statement:
--   If a source has not yet been selected, its entire fibre is disjoint from
--   the current source carrier.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L408-L424
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L408-L424

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxSourceCarrier_disjoint_fiber_of_not_mem
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (R : Finset V) {s : V} (hs : s ∉ R) :
    Disjoint
      (auxSourceCarrier C ambientRoot hScores R)
      (auxSourceFiber C ambientRoot hScores s) := by sorry
