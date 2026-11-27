-- Prove2me | Theorems.Thm_TreeStack_taskGainSum_partition
-- name    : TreeStack.taskGainSum_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:29:11.919206+00:00
-- url     : https://prove2.me/theorems/d4b2b3d9-3f77-4e96-b75a-06f61469a308
-- title:
--   Tree Stack: task Gain Sum partition
-- statement:
--   Positive, zero, and negative filtering preserves the total task gain.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L227-L256
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L227-L256

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {α : Type*}

theorem TreeStack.taskGainSum_partition (gain : α → ℤ) (tasks : List α) :
    taskGainSum gain (positiveTasks gain tasks) +
        taskGainSum gain (zeroTasks gain tasks) +
        taskGainSum gain (negativeTasks gain tasks) =
      taskGainSum gain tasks := by sorry
