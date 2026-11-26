-- Prove2me | Theorems.Thm_TreeStack_erase_root_eq_leaf_union_internal
-- name    : TreeStack.erase_root_eq_leaf_union_internal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:05:57.312828+00:00
-- url     : https://prove2.me/theorems/9f9b59b3-319c-5325-a54a-638b725f5ab9
-- title:
--   Tree Stack: erase root eq leaf union internal
-- statement:
--   If all degrees are positive, every non-root vertex is either a leaf or
--   a non-root internal vertex.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L85-L95
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L85-L95

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical

theorem TreeStack.erase_root_eq_leaf_union_internal {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V)
    (hdeg : ∀ v, 0 < T.graph.degree v) :
    (Finset.univ : Finset V).erase r =
      leafVertices T r ∪ nonRootInternalVertices T r := by sorry
