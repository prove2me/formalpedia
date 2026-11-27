-- Prove2me | Theorems.Thm_TreeStack_executeRootTaskSchedule
-- name    : TreeStack.executeRootTaskSchedule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:35:29.849731+00:00
-- url     : https://prove2.me/theorems/e78e1789-5ff2-4a0d-b91c-734a258fe8c1
-- title:
--   Tree Stack: execute Root Task Schedule
-- statement:
--   Execute a safe list of occupied incident branches toward one target root.
--   Every task attains its exact branch message gain; distinct incident interiors
--   are preserved by locality.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L349-L504
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L349-L504

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.executeRootTaskSchedule
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    ∀ (tasks : List (RootTask T C r)) (E : Configuration V),
      tasks.Nodup →
      (∀ t ∈ tasks, ∀ v ∈ t.branch.vertices, E v = C v) →
      TaskScheduleSafe
        (fun t : RootTask T C r => t.gain)
        (E r : ℤ) tasks →
      ∃ D : Configuration V,
        Reach T.graph E D ∧
        (D r : ℤ) =
          (E r : ℤ) +
            taskGainSum (fun t : RootTask T C r => t.gain) tasks ∧
        (∀ t ∈ tasks, t.branch.Cleared D) ∧
        (∀ (u : V) (h : T.graph.Adj u r),
          (∀ t ∈ tasks, t.1 ≠ u) →
          ∀ v ∈ (incidentBranch T r u h).vertices, D v = E v) := by sorry
