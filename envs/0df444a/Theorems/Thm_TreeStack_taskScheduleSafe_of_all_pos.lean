-- Prove2me | Theorems.Thm_TreeStack_taskScheduleSafe_of_all_pos
-- name    : TreeStack.taskScheduleSafe_of_all_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:28:52.68049+00:00
-- url     : https://prove2.me/theorems/a2d0a453-894b-5898-ac86-d0c8534c8b18
-- title:
--   Tree Stack: task Schedule Safe of all pos
-- statement:
--   The Tree Stack construction uses the task Schedule Safe of all pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L167-L182
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L167-L182

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {α : Type*}

theorem TreeStack.taskScheduleSafe_of_all_pos (gain : α → ℤ) :
    ∀ {a : ℤ} {tasks : List α},
      0 ≤ a →
      (∀ t ∈ tasks, 0 < gain t) →
      TaskScheduleSafe gain a tasks
  := by sorry
