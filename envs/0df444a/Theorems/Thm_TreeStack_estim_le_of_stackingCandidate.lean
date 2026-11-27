-- Prove2me | Theorems.Thm_TreeStack_estim_le_of_stackingCandidate
-- name    : TreeStack.estim_le_of_stackingCandidate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:30.727171+00:00
-- url     : https://prove2.me/theorems/f29a5f6f-853c-540b-94c3-8b31a897a737
-- title:
--   Tree Stack: estim le of stacking Candidate
-- statement:
--   Every admissible exact stacking threshold is at least the estimator.
--   Otherwise exact-size upward closure would make the estimator-minus-one
--   obstruction stackable.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Stacking.lean#L74-L87
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Stacking.lean#L74-L87

import Mathlib
import Definitions.Def_TreeStack_UpperBound
import Definitions.Def_TreeStack_Stacking
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.estim_le_of_stackingCandidate
    [Nontrivial V] (T : FiniteTree V) {t : ℕ}
    (ht : StackingCandidate T t) :
    estim T ≤ t := by sorry
