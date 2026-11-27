-- Prove2me | Theorems.Thm_TreeStack_taskGainSum_eq_list_sum
-- name    : TreeStack.taskGainSum_eq_list_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:28:21.039577+00:00
-- url     : https://prove2.me/theorems/f9cc127e-dc95-5a7d-b861-327fb8587a54
-- title:
--   Tree Stack: task Gain Sum eq list sum
-- statement:
--   The recursive task sum is the ordinary sum of the mapped list.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L96-L101
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L96-L101

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {α : Type*}

theorem TreeStack.taskGainSum_eq_list_sum (gain : α → ℤ) :
    ∀ tasks : List α,
      taskGainSum gain tasks = (tasks.map gain).sum
  := by sorry
