-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxDartMessageTerm_add_symm
-- name    : TreeStack.OrientedBranch.auxDartMessageTerm_add_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:14:49.353695+00:00
-- url     : https://prove2.me/theorems/2b031ba2-1fb5-515a-bf86-1b76e72980a0
-- title:
--   Oriented Branch: aux Dart Message Term add symm
-- statement:
--   The two dart terms of an edge are exactly the negative of its auxiliary
--   edge contribution.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L339-L349
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L339-L349

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxDartMessageTerm_add_symm
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (e : T.graph.edgeFinset) :
    auxDartMessageTerm C ambientRoot hScores (edgeDart e) +
        auxDartMessageTerm C ambientRoot hScores (edgeDart e).symm =
      -auxEdgeContribution C ambientRoot hScores (edgeBranch e) := by sorry
