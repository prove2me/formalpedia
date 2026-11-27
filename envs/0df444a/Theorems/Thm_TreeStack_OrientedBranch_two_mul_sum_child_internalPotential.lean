-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_two_mul_sum_child_internalPotential
-- name    : TreeStack.OrientedBranch.two_mul_sum_child_internalPotential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:51:05.698635+00:00
-- url     : https://prove2.me/theorems/5a996aed-de92-4308-bb95-b0666e009601
-- title:
--   Oriented Branch: two mul sum child internal Potential
-- statement:
--   Doubling the total child potential exactly recovers the parent-rooted
--   potential of all non-root branch vertices.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L446-L486
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L446-L486

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.two_mul_sum_child_internalPotential (B : OrientedBranch T) :
    2 * (∑ c : B.Child, (B.childBranch c).internalPotential) =
      ∑ x ∈ B.vertices.erase B.root,
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist B.root x
        else
          0 := by sorry
