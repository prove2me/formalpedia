-- Prove2me | Theorems.Thm_TreeStack_stackableAt_of_stackedAt
-- name    : TreeStack.stackableAt_of_stackedAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:07:10.995253+00:00
-- url     : https://prove2.me/theorems/15ea2291-cd34-5d0d-9d79-465abdc2917f
-- title:
--   Tree Stack: stackable At of stacked At
-- statement:
--   A stack is already stackable without making a move.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L60-L63
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L60-L63

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove
set_option autoImplicit false
open TreeStack

theorem TreeStack.stackableAt_of_stackedAt {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (C : Configuration V) (r : V) (h : StackedAt C r) :
    StackableAt G C r := by sorry
