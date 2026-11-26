-- Prove2me | Theorems.Thm_TreeStack_card_internal_le_weighted_sum
-- name    : TreeStack.card_internal_le_weighted_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:02.358476+00:00
-- url     : https://prove2.me/theorems/1fa9bbaa-09f6-52fd-bee3-01015436efe3
-- title:
--   Tree Stack: card internal le weighted sum
-- statement:
--   Each weighted non-root internal contribution is at least one.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L116-L132
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L116-L132

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical

theorem TreeStack.card_internal_le_weighted_sum {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    (nonRootInternalVertices T r).card ≤
      ∑ v ∈ nonRootInternalVertices T r,
        T.graph.degree v * 2 ^ T.graph.dist r v := by sorry
