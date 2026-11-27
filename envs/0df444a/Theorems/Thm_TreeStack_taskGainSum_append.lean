-- Prove2me | Theorems.Thm_TreeStack_taskGainSum_append
-- name    : TreeStack.taskGainSum_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:27:13.5542+00:00
-- url     : https://prove2.me/theorems/757e2852-4fd2-5b43-b45e-d8d86dcfc86c
-- title:
--   Tree Stack: task Gain Sum append
-- statement:
--   The Tree Stack construction uses the task Gain Sum append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L134-L141
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L134-L141

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {α : Type*}

theorem TreeStack.taskGainSum_append (gain : α → ℤ) (xs ys : List α) :
    taskGainSum gain (xs ++ ys) =
      taskGainSum gain xs + taskGainSum gain ys := by sorry
