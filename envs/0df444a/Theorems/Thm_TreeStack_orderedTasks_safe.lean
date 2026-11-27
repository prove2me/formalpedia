-- Prove2me | Theorems.Thm_TreeStack_orderedTasks_safe
-- name    : TreeStack.orderedTasks_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:29:12.981421+00:00
-- url     : https://prove2.me/theorems/fce235b5-408d-5633-b99c-f38890a71c98
-- title:
--   Tree Stack: ordered Tasks safe
-- statement:
--   Positive/zero/negative scheduling lemma from the audited construction.
--   If the starting pile is nonnegative and the final total is positive, placing
--   positive tasks first, zero tasks next, and negative tasks last makes every
--   individual task executable.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L342-L382
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L342-L382

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {α : Type*}

theorem TreeStack.orderedTasks_safe (gain : α → ℤ) (tasks : List α) (a : ℤ)
    (ha : 0 ≤ a)
    (hfinal : 0 < a + taskGainSum gain tasks) :
    TaskScheduleSafe gain a (orderedTasks gain tasks) := by sorry
