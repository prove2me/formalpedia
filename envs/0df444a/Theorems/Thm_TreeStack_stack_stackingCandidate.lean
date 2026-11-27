-- Prove2me | Theorems.Thm_TreeStack_stack_stackingCandidate
-- name    : TreeStack.stack_stackingCandidate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:40.173405+00:00
-- url     : https://prove2.me/theorems/a1ce62d9-488f-4d0c-99ea-1561564a84a9
-- title:
--   Tree Stack: stack stacking Candidate
-- statement:
--   The defined stacking number is itself an exact-size stacking candidate.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Stacking.lean#L57-L61
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Stacking.lean#L57-L61

import Mathlib
import Definitions.Def_TreeStack_UpperBound
import Definitions.Def_TreeStack_Stacking
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.stack_stackingCandidate
    [Nontrivial V] (T : FiniteTree V) :
    StackingCandidate T (stack T) := by sorry
