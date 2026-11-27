-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_defectEdgeState_of_supportEdge
-- name    : TreeStack.OrientedBranch.defectEdgeState_of_supportEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:01:43.092474+00:00
-- url     : https://prove2.me/theorems/e495fa0e-d506-58e4-b686-e49e59ef67c4
-- title:
--   Oriented Branch: defect Edge State of support Edge
-- statement:
--   The already-proved local defect classification applies directly to every
--   retained support edge, without changing the ambient vertex type.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L240-L250
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L240-L250

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.defectEdgeState_of_supportEdge
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C)
    (hScores : ∀ v, score T C v ≤ 0) :
    DefectEdgeState
      (messageContribution (branchMessage C B))
      (messageContribution (branchMessage C B.reverseBranch))
      (scoreDefect T C B.root)
      (scoreDefect T C B.parent) := by sorry
