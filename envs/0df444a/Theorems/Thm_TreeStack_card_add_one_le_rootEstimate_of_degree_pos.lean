-- Prove2me | Theorems.Thm_TreeStack_card_add_one_le_rootEstimate_of_degree_pos
-- name    : TreeStack.card_add_one_le_rootEstimate_of_degree_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:23.526006+00:00
-- url     : https://prove2.me/theorems/0b67bdab-e800-5ab2-9959-9fa53ca05ba2
-- title:
--   Tree Stack: card add one le root Estimate of degree pos
-- statement:
--   Arithmetic form of the elementary estimator lower bound, assuming
--   positive degree at every vertex.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L136-L148
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L136-L148

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical

theorem TreeStack.card_add_one_le_rootEstimate_of_degree_pos
    {V : Type*} [Fintype V] (T : FiniteTree V) (r : V)
    (hdeg : ∀ v, 0 < T.graph.degree v) :
    Fintype.card V + 1 ≤ rootEstimate T r := by sorry
