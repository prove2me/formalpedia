-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_exists_global_heightDominatingRoot_from_sourceCarrier
-- name    : TreeStack.OrientedBranch.exists_global_heightDominatingRoot_from_sourceCarrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:18.212395+00:00
-- url     : https://prove2.me/theorems/d7d20e72-21f6-5b0d-9246-fb3fb4c0192a
-- title:
--   Oriented Branch: exists global height Dominating Root from source Carrier
-- statement:
--   Starting from any nonempty connected union of canonical source
--   fibres whose auxiliary height is dominated by one root, repeatedly adjoin the
--   source fibre across a boundary edge.  The process terminates when the carrier
--   is all vertices and returns one ambient root dominating every auxiliary
--   height.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L454-L541
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L454-L541

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.exists_global_heightDominatingRoot_from_sourceCarrier
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (R : Finset V) (r : V)
    (hConn :
      TreePathConnected (T := T)
        (auxSourceCarrier C ambientRoot hScores R))
    (hDom :
      HeightDominated (T := T)
        (fun v => auxHeight C ambientRoot hScores v)
        (auxSourceCarrier C ambientRoot hScores R) r) :
    ∃ t : V, ∀ v : V,
      auxHeight C ambientRoot hScores v ≤ T.graph.dist t v := by sorry
