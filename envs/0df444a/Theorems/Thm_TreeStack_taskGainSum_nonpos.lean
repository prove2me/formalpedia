-- Prove2me | Theorems.Thm_TreeStack_taskGainSum_nonpos
-- name    : TreeStack.taskGainSum_nonpos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:28:45.312828+00:00
-- url     : https://prove2.me/theorems/fe68c5ca-5b98-5cfd-a1c0-659989e5c88e
-- title:
--   Tree Stack: task Gain Sum nonpos
-- statement:
--   The Tree Stack construction uses the task Gain Sum nonpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L153-L165
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L153-L165

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {α : Type*}

theorem TreeStack.taskGainSum_nonpos (gain : α → ℤ) :
    ∀ tasks : List α,
      (∀ t ∈ tasks, gain t ≤ 0) →
      taskGainSum gain tasks ≤ 0
  := by sorry
