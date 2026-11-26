-- Prove2me | Theorems.Thm_TreeStack_leafVertices_disjoint_internal
-- name    : TreeStack.leafVertices_disjoint_internal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:01.440527+00:00
-- url     : https://prove2.me/theorems/6d18ad03-530a-5e4f-8169-01562728beba
-- title:
--   Tree Stack: leaf Vertices disjoint internal
-- statement:
--   The Tree Stack construction uses the leaf Vertices disjoint internal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L97-L104
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L97-L104

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical

theorem TreeStack.leafVertices_disjoint_internal {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    Disjoint (leafVertices T r) (nonRootInternalVertices T r) := by sorry
