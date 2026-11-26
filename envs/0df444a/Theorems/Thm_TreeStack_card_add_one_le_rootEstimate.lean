-- Prove2me | Theorems.Thm_TreeStack_card_add_one_le_rootEstimate
-- name    : TreeStack.card_add_one_le_rootEstimate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:06:27.870361+00:00
-- url     : https://prove2.me/theorems/6bab8ea7-6d1c-42ab-bbe1-025213fc5b31
-- title:
--   Tree Stack: card add one le root Estimate
-- statement:
--   Elementary estimator lower bound for every root of a nontrivial finite
--   tree.  The root may itself have degree one.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L152-L157
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L152-L157

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical

theorem TreeStack.card_add_one_le_rootEstimate {V : Type*} [Fintype V] [Nontrivial V]
    (T : FiniteTree V) (r : V) :
    Fintype.card V + 1 ≤ rootEstimate T r := by sorry
