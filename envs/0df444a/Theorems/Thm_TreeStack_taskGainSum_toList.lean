-- Prove2me | Theorems.Thm_TreeStack_taskGainSum_toList
-- name    : TreeStack.taskGainSum_toList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:28:23.260805+00:00
-- url     : https://prove2.me/theorems/70e48c02-3688-578d-9d3e-a268fb8ec198
-- title:
--   Tree Stack: task Gain Sum to List
-- statement:
--   The list sum agrees with the corresponding finite-set sum.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L104-L108
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L104-L108

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {α : Type*}

theorem TreeStack.taskGainSum_toList [DecidableEq α]
    (gain : α → ℤ) (s : Finset α) :
    taskGainSum gain s.toList = Finset.sum s gain := by sorry
