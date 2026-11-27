-- Prove2me | Theorems.Thm_TreeStack_executeAllRootTasks
-- name    : TreeStack.executeAllRootTasks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:35:36.184812+00:00
-- url     : https://prove2.me/theorems/ca087ca5-3376-493e-9500-02f6e9b0f418
-- title:
--   Tree Stack: execute All Root Tasks
-- statement:
--   Execute every occupied incident branch in the audited order.  The result
--   clears every non-root vertex and leaves exactly the rooted score at r.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L508-L594
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L508-L594

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.executeAllRootTasks
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (hSafe :
      TaskScheduleSafe
        (fun t : RootTask T C r => t.gain)
        (C r : ℤ)
        (orderedTasks
          (fun t : RootTask T C r => t.gain)
          (rootTasks T C r))) :
    ∃ D : Configuration V,
      Reach T.graph C D ∧
      (D r : ℤ) = score T C r ∧
      (∀ v : V, v ≠ r → D v = 0) := by sorry
