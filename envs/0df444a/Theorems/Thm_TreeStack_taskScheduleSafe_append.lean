-- Prove2me | Theorems.Thm_TreeStack_taskScheduleSafe_append
-- name    : TreeStack.taskScheduleSafe_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:28:33.686967+00:00
-- url     : https://prove2.me/theorems/e8a5e391-a0c1-50be-a4a8-f5f2b70bffd1
-- title:
--   Tree Stack: task Schedule Safe append
-- statement:
--   The Tree Stack construction uses the task Schedule Safe append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L143-L151
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L143-L151

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {α : Type*}

theorem TreeStack.taskScheduleSafe_append (gain : α → ℤ) (a : ℤ)
    (xs ys : List α) :
    TaskScheduleSafe gain a (xs ++ ys) ↔
      TaskScheduleSafe gain a xs ∧
        TaskScheduleSafe gain (a + taskGainSum gain xs) ys := by sorry
