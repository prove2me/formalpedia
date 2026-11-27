-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxSourceCarrier_univ
-- name    : TreeStack.OrientedBranch.auxSourceCarrier_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:33:21.068823+00:00
-- url     : https://prove2.me/theorems/3b20678c-cb1e-5af1-b919-74016629dbda
-- title:
--   Oriented Branch: aux Source Carrier univ
-- statement:
--   Selecting every source gives the whole ambient vertex set.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L398-L404
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L398-L404

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxSourceCarrier_univ
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxSourceCarrier C ambientRoot hScores (Finset.univ : Finset V) =
      (Finset.univ : Finset V) := by sorry
