-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_sum_dite_children
-- name    : TreeStack.OrientedBranch.sum_dite_children
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:50:49.703782+00:00
-- url     : https://prove2.me/theorems/9212fa8f-2156-4c80-a2e1-29f813b00ff7
-- title:
--   Oriented Branch: sum dite children
-- statement:
--   A dependent sum over genuine child vertices agrees with the corresponding
--   sum over the finite child type.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L351-L395
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L351-L395

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.sum_dite_children {M : Type*} [AddCommMonoid M]
    (B : OrientedBranch T) (f : B.Child → M) :
    (∑ v : V,
      if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
        f { vertex := v, adj := h.1, ne_parent := h.2 }
      else
        0) =
      ∑ c : B.Child, f c := by sorry
