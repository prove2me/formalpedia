-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxInternalDegreePotential_le_rootedInternalPotential
-- name    : TreeStack.OrientedBranch.auxInternalDegreePotential_le_rootedInternalPotential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:49.060468+00:00
-- url     : https://prove2.me/theorems/c41d4fc4-5454-49b4-9fed-ea607453ba0e
-- title:
--   Oriented Branch: aux Internal Degree Potential le rooted Internal Potential
-- statement:
--   Once one root dominates all auxiliary heights, the weighted internal
--   degree potential is bounded by the rooted internal estimator potential.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/UpperBound.lean#L30-L53
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/UpperBound.lean#L30-L53

import Mathlib
import Definitions.Def_TreeStack_Consolidation
import Definitions.Def_TreeStack_UpperBound
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxInternalDegreePotential_le_rootedInternalPotential
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r : V)
    (hHeight : ∀ v,
      auxHeight C ambientRoot hScores v ≤ T.graph.dist r v) :
    auxInternalDegreePotential C ambientRoot hScores ≤
      (rootedInternalPotential T r : ℤ) := by sorry
