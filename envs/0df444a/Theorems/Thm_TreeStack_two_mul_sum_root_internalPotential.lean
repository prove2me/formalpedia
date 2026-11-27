-- Prove2me | Theorems.Thm_TreeStack_two_mul_sum_root_internalPotential
-- name    : TreeStack.two_mul_sum_root_internalPotential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:51:38.499491+00:00
-- url     : https://prove2.me/theorems/cd9c24e5-875e-4877-a567-c1a9acde128e
-- title:
--   Tree Stack: two mul sum root internal Potential
-- statement:
--   Doubling all incident branch potentials recovers the root-distance
--   potential of every non-root internal vertex.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1154-L1196
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1154-L1196

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.two_mul_sum_root_internalPotential
    (T : FiniteTree V) (r : V) :
    2 * (∑ n : RootNeighbor T r, n.branch.internalPotential) =
      ∑ x ∈ (Finset.univ : Finset V).erase r,
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist r x
        else
          0 := by sorry
