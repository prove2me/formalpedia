-- Prove2me | Theorems.Thm_TreeStack_sum_dite_rootNeighbors
-- name    : TreeStack.sum_dite_rootNeighbors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:47:02.491448+00:00
-- url     : https://prove2.me/theorems/c2de239b-a6e8-4fc5-86ec-fb529d4e26ca
-- title:
--   Tree Stack: sum dite root Neighbors
-- statement:
--   A dependent sum over root neighbors agrees with the corresponding sum over
--   the finite subtype of actual neighbors.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1061-L1101
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1061-L1101

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.sum_dite_rootNeighbors {M : Type*} [AddCommMonoid M]
    (T : FiniteTree V) (r : V) (f : RootNeighbor T r → M) :
    (∑ u : V,
      if h : T.graph.Adj u r then
        f ⟨u, h⟩
      else
        0) =
      ∑ n : RootNeighbor T r, f n := by sorry
