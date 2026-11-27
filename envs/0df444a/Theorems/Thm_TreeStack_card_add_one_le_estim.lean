-- Prove2me | Theorems.Thm_TreeStack_card_add_one_le_estim
-- name    : TreeStack.card_add_one_le_estim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:07:11.568492+00:00
-- url     : https://prove2.me/theorems/933ad542-4b17-4491-98f4-6b71cfd11c2c
-- title:
--   Tree Stack: card add one le estim
-- statement:
--   The tree estimator is at least one more than the vertex count for every
--   nontrivial finite tree.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L168-L172
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L168-L172

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical

theorem TreeStack.card_add_one_le_estim {V : Type*} [Fintype V] [Nontrivial V]
    (T : FiniteTree V) :
    Fintype.card V + 1 ≤ estim T := by sorry
