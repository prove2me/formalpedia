-- Prove2me | Theorems.Thm_TreeStack_taskGainSum_rootTasks
-- name    : TreeStack.taskGainSum_rootTasks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:31:17.866437+00:00
-- url     : https://prove2.me/theorems/2d4bb5a5-5057-5851-9456-b3ceb1c403df
-- title:
--   Tree Stack: task Gain Sum root Tasks
-- statement:
--   Rooted executable task gains sum to the full rooted message sum.
--   Configuration-empty branches contribute zero to the mathematical sum but
--   never appear as tasks.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L279-L315
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L279-L315

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.taskGainSum_rootTasks
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    taskGainSum
        (fun t : RootTask T C r => t.gain)
        (rootTasks T C r) =
      rootMessageSum T C r := by sorry
