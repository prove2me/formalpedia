-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_executeOccupiedTaskSchedule
-- name    : TreeStack.OrientedBranch.executeOccupiedTaskSchedule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:32:50.931404+00:00
-- url     : https://prove2.me/theorems/a6f1f31f-35b8-5652-8d2a-94dd502d19b0
-- title:
--   Oriented Branch: execute Occupied Task Schedule
-- statement:
--   Execute a safe list of occupied child tasks by recursively attaining each
--   child's exact boundary gain.  The theorem records the parent-root gain,
--   preservation of the external boundary, clearing of every scheduled child, and
--   pointwise preservation of every sibling omitted from the list.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L970-L1148
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L970-L1148

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

theorem TreeStack.OrientedBranch.executeOccupiedTaskSchedule
    (B : OrientedBranch T) (C : Configuration V)
    (hChildAttain :
      ∀ (c : B.Child) (E : Configuration V) (d : ℤ) (q : ℕ),
        (B.childBranch c).Occupied E →
        branchMessage E (B.childBranch c) = some d →
        0 < (q : ℤ) + d →
        ∃ D : Configuration V,
          (B.childBranch c).ClearOutcome E q D ∧
            (D B.root : ℤ) = (q : ℤ) + d) :
    ∀ (tasks : List (B.OccupiedChild C)) (E : Configuration V),
      tasks.Nodup →
      (∀ t ∈ tasks, ∀ v ∈ (B.childBranch t.child).vertices,
        E v = C v) →
      TaskScheduleSafe
        (fun t : B.OccupiedChild C => t.gain)
        (E B.root : ℤ) tasks →
      ∃ D : Configuration V,
        B.BranchReach E D ∧
        (D B.root : ℤ) =
          (E B.root : ℤ) +
            taskGainSum
              (fun t : B.OccupiedChild C => t.gain) tasks ∧
        D B.parent = E B.parent ∧
        (∀ t ∈ tasks, (B.childBranch t.child).Cleared D) ∧
        (∀ c : B.Child,
          (∀ t ∈ tasks, t.1 ≠ c.vertex) →
          ∀ v ∈ (B.childBranch c).vertices, D v = E v) := by sorry
