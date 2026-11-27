-- Prove2me | Theorems.Thm_TreeStack_stack_le_of_stackingCandidate
-- name    : TreeStack.stack_le_of_stackingCandidate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:30.947122+00:00
-- url     : https://prove2.me/theorems/80d838fe-6a7b-47d1-8ed4-d522ac8b026b
-- title:
--   Tree Stack: stack le of stacking Candidate
-- statement:
--   Minimality of the exact-size stacking number.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Stacking.lean#L64-L69
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Stacking.lean#L64-L69

import Mathlib
import Definitions.Def_TreeStack_UpperBound
import Definitions.Def_TreeStack_Stacking
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.stack_le_of_stackingCandidate
    [Nontrivial V] (T : FiniteTree V) {t : ℕ}
    (ht : StackingCandidate T t) :
    stack T ≤ t := by sorry
