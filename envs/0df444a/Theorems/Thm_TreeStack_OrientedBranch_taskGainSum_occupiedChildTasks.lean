-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_taskGainSum_occupiedChildTasks
-- name    : TreeStack.OrientedBranch.taskGainSum_occupiedChildTasks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:28:08.173746+00:00
-- url     : https://prove2.me/theorems/129cee62-31df-45e2-9874-67cbeeda9a91
-- title:
--   Oriented Branch: task Gain Sum occupied Child Tasks
-- statement:
--   The occupied executable tasks carry exactly the recursive child-message
--   sum. Empty genuine children contribute zero to childMessageSum but are absent
--   from the task list.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L922-L958
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L922-L958

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]

theorem TreeStack.OrientedBranch.taskGainSum_occupiedChildTasks
    (B : OrientedBranch T) (C : Configuration V) :
    taskGainSum
        (fun t : B.OccupiedChild C => t.gain)
        (B.occupiedChildTasks C) =
      childMessageSum C B := by sorry
