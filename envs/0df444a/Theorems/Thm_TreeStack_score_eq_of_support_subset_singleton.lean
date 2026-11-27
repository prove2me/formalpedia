-- Prove2me | Theorems.Thm_TreeStack_score_eq_of_support_subset_singleton
-- name    : TreeStack.score_eq_of_support_subset_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:54:45.512856+00:00
-- url     : https://prove2.me/theorems/aa9aa0d3-20fc-4b13-b8f7-66de809bd9e9
-- title:
--   Tree Stack: score eq of support subset singleton
-- statement:
--   If all positive piles are concentrated at one vertex, that vertex's rooted
--   score is exactly its pile size.  Every incident branch is genuinely empty,
--   not an integer-message zero branch.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L362-L380
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L362-L380

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical

theorem TreeStack.score_eq_of_support_subset_singleton
    {V : Type*} [Fintype V]
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (hSupport : ∀ v, 0 < C v → v = r) :
    score T C r = (C r : ℤ) := by sorry
