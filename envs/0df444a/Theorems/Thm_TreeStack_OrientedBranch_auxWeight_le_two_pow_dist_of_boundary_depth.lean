-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxWeight_le_two_pow_dist_of_boundary_depth
-- name    : TreeStack.OrientedBranch.auxWeight_le_two_pow_dist_of_boundary_depth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:33:29.628525+00:00
-- url     : https://prove2.me/theorems/f964ab93-a066-4ad4-a2a6-34c08b95fa5e
-- title:
--   Oriented Branch: aux Weight le two pow dist of boundary depth
-- statement:
--   Under the same boundary-depth comparison, the first source's rooted
--   power-of-two weight pointwise dominates the auxiliary weight throughout the
--   second fibre.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L704-L721
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L704-L721

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxWeight_le_two_pow_dist_of_boundary_depth
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r s a b v : V}
    (hrs : r ≠ s)
    (ha : a ∈ auxSourceFiber C ambientRoot hScores r)
    (hb : b ∈ auxSourceFiber C ambientRoot hScores s)
    (hadj : T.graph.Adj a b)
    (hDepth :
      T.graph.dist s b ≤ T.graph.dist r a + 1)
    (hv : v ∈ auxSourceFiber C ambientRoot hScores s) :
    auxWeight C ambientRoot hScores v ≤
      2 ^ T.graph.dist r v := by sorry
