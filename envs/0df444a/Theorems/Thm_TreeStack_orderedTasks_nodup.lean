-- Prove2me | Theorems.Thm_TreeStack_orderedTasks_nodup
-- name    : TreeStack.orderedTasks_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:29:48.362498+00:00
-- url     : https://prove2.me/theorems/160e4dfe-8dad-449a-804c-1de44b513cae
-- title:
--   Tree Stack: ordered Tasks nodup
-- statement:
--   The Tree Stack construction uses the ordered Tasks nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L300-L336
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L300-L336

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {α : Type*}

theorem TreeStack.orderedTasks_nodup (gain : α → ℤ) {tasks : List α}
    (h : tasks.Nodup) :
    (orderedTasks gain tasks).Nodup := by sorry
