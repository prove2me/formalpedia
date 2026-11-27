-- Prove2me | Theorems.Thm_TreeStack_stack_eq_estim
-- name    : TreeStack.stack_eq_estim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:41.983982+00:00
-- url     : https://prove2.me/theorems/92221838-6f2e-4828-8e36-738cfee9ebe5
-- title:
--   Tree Stack: stack eq estim
-- statement:
--   Exact Csernák--Soukup stacking equality for every nontrivial finite
--   tree.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Stacking.lean#L91-L96
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Stacking.lean#L91-L96

import Mathlib
import Definitions.Def_TreeStack_UpperBound
import Definitions.Def_TreeStack_Stacking
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.stack_eq_estim
    [Nontrivial V] (T : FiniteTree V) :
    stack T = estim T := by sorry
