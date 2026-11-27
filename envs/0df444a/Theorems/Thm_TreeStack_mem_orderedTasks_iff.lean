-- Prove2me | Theorems.Thm_TreeStack_mem_orderedTasks_iff
-- name    : TreeStack.mem_orderedTasks_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:29:35.563021+00:00
-- url     : https://prove2.me/theorems/9289402d-96f3-4290-aeb0-2d1b872c9690
-- title:
--   Tree Stack: mem ordered Tasks iff
-- statement:
--   The Tree Stack construction uses the mem ordered Tasks iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L264-L298
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L264-L298

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {α : Type*}

theorem TreeStack.mem_orderedTasks_iff (gain : α → ℤ) (tasks : List α) (t : α) :
    t ∈ orderedTasks gain tasks ↔ t ∈ tasks := by sorry
