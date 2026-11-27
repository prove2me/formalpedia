-- Prove2me | Theorems.Thm_TreeStack_taskScheduleSafe_of_all_nonpos_of_final_pos
-- name    : TreeStack.taskScheduleSafe_of_all_nonpos_of_final_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:29:00.201872+00:00
-- url     : https://prove2.me/theorems/9b32e86a-b720-5fd5-9bd4-8b2949aa2d29
-- title:
--   Tree Stack: task Schedule Safe of all nonpos of final pos
-- statement:
--   The Tree Stack construction uses the task Schedule Safe of all nonpos of final pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L202-L224
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L202-L224

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {α : Type*}

theorem TreeStack.taskScheduleSafe_of_all_nonpos_of_final_pos
    (gain : α → ℤ) :
    ∀ {a : ℤ} {tasks : List α},
      0 < a + taskGainSum gain tasks →
      (∀ t ∈ tasks, gain t ≤ 0) →
      TaskScheduleSafe gain a tasks
  := by sorry
