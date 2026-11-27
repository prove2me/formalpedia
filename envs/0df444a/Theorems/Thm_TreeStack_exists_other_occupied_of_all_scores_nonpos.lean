-- Prove2me | Theorems.Thm_TreeStack_exists_other_occupied_of_all_scores_nonpos
-- name    : TreeStack.exists_other_occupied_of_all_scores_nonpos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:02:44.768794+00:00
-- url     : https://prove2.me/theorems/bd9331c5-2bd7-5abd-a2ac-3bfaa92c8516
-- title:
--   Tree Stack: exists other occupied of all scores nonpos
-- statement:
--   Under all-nonpositive scores, every occupied vertex has another distinct
--   occupied vertex.  In particular, a nonzero counterconfiguration cannot have
--   singleton support.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L385-L400
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L385-L400

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical

theorem TreeStack.exists_other_occupied_of_all_scores_nonpos
    {V : Type*} [Fintype V]
    (T : FiniteTree V) (C : Configuration V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r : V} (hr : 0 < C r) :
    ∃ v, v ≠ r ∧ 0 < C v := by sorry
