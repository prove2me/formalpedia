-- Prove2me | Theorems.Thm_TreeStack_estim_stackingCandidate
-- name    : TreeStack.estim_stackingCandidate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:45.354867+00:00
-- url     : https://prove2.me/theorems/33fdad6e-4747-4e77-9de1-2ec0e5ecd2b4
-- title:
--   Tree Stack: estim stacking Candidate
-- statement:
--   On every nontrivial finite tree the estimator itself is an admissible
--   stacking candidate.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Stacking.lean#L39-L47
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Stacking.lean#L39-L47

import Mathlib
import Definitions.Def_TreeStack_UpperBound
import Definitions.Def_TreeStack_Stacking
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.estim_stackingCandidate
    [Nontrivial V] (T : FiniteTree V) :
    StackingCandidate T (estim T) := by sorry
