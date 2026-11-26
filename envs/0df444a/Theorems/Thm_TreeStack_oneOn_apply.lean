-- Prove2me | Theorems.Thm_TreeStack_oneOn_apply
-- name    : TreeStack.oneOn_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:01.010924+00:00
-- url     : https://prove2.me/theorems/eceb102d-27ec-426d-b228-c9cc9e169da0
-- title:
--   Tree Stack: one On apply
-- statement:
--   The Tree Stack construction uses the one On apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L77-L78
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L77-L78

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove
set_option autoImplicit false
open TreeStack

theorem TreeStack.oneOn_apply {V : Type*} [DecidableEq V] (s : Finset V) (v : V) :
    oneOn s v = if v ∈ s then 1 else 0 := by sorry

attribute [defeq] TreeStack.oneOn_apply
