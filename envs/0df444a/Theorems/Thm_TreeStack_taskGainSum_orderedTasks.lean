-- Prove2me | Theorems.Thm_TreeStack_taskGainSum_orderedTasks
-- name    : TreeStack.taskGainSum_orderedTasks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:27:36.276846+00:00
-- url     : https://prove2.me/theorems/ea391b90-8fa5-4434-a5df-ca029fbb6293
-- title:
--   Tree Stack: task Gain Sum ordered Tasks
-- statement:
--   The Tree Stack construction uses the task Gain Sum ordered Tasks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L258-L262
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L258-L262

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {α : Type*}

theorem TreeStack.taskGainSum_orderedTasks (gain : α → ℤ) (tasks : List α) :
    taskGainSum gain (orderedTasks gain tasks) =
      taskGainSum gain tasks := by sorry
