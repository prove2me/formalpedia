-- Prove2me | Theorems.Thm_TreeStack_not_stackable_iff_all_scores_nonpos
-- name    : TreeStack.not_stackable_iff_all_scores_nonpos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:36:14.877185+00:00
-- url     : https://prove2.me/theorems/47980c20-b56d-59d7-994a-2f298c4b991f
-- title:
--   Tree Stack: not stackable iff all scores nonpos
-- statement:
--   Global non-stackability is equivalent to every rooted score being
--   nonpositive.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L831-L846
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L831-L846

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.not_stackable_iff_all_scores_nonpos
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) :
    ¬ Stackable T.graph C ↔ ∀ r : V, score T C r ≤ 0 := by sorry
