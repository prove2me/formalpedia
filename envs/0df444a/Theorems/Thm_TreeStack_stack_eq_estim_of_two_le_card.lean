-- Prove2me | Theorems.Thm_TreeStack_stack_eq_estim_of_two_le_card
-- name    : TreeStack.stack_eq_estim_of_two_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:34:49.888884+00:00
-- url     : https://prove2.me/theorems/d4d984de-2d3d-5c3f-a6aa-feb58f907ffa
-- title:
--   Tree Stack: stack eq estim of two le card
-- statement:
--   Headline form with the source's explicit nontriviality hypothesis.  The
--   one-vertex tree is intentionally excluded because the source stacking number
--   uses thresholds at least two while the displayed estimator is one there.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Stacking.lean#L101-L107
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Stacking.lean#L101-L107

import Mathlib
import Definitions.Def_TreeStack_UpperBound
import Definitions.Def_TreeStack_Stacking
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.stack_eq_estim_of_two_le_card
    (T : FiniteTree V)
    (hcard : 2 ≤ Fintype.card V) :
    stack T = estim T := by sorry
