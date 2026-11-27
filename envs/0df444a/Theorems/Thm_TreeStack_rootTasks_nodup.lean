-- Prove2me | Theorems.Thm_TreeStack_rootTasks_nodup
-- name    : TreeStack.rootTasks_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:35:21.201628+00:00
-- url     : https://prove2.me/theorems/44f486da-7b5a-5a20-b01b-220f45568c3f
-- title:
--   Tree Stack: root Tasks nodup
-- statement:
--   The Tree Stack construction uses the root Tasks nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L263-L267
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L263-L267

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.rootTasks_nodup
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    (rootTasks T C r).Nodup := by sorry
