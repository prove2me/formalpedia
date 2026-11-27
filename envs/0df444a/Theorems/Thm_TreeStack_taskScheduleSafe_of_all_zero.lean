-- Prove2me | Theorems.Thm_TreeStack_taskScheduleSafe_of_all_zero
-- name    : TreeStack.taskScheduleSafe_of_all_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:36:50.615811+00:00
-- url     : https://prove2.me/theorems/c35b0c0d-725d-411f-bb60-750f00e350d8
-- title:
--   Tree Stack: task Schedule Safe of all zero
-- statement:
--   The Tree Stack construction uses the task Schedule Safe of all zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L184-L200
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L184-L200

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {α : Type*}

theorem TreeStack.taskScheduleSafe_of_all_zero (gain : α → ℤ) :
    ∀ {a : ℤ} {tasks : List α},
      0 < a →
      (∀ t ∈ tasks, gain t = 0) →
      TaskScheduleSafe gain a tasks
  := by sorry
