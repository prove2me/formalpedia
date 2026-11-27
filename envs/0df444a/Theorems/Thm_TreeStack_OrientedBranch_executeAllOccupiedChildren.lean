-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_executeAllOccupiedChildren
-- name    : TreeStack.OrientedBranch.executeAllOccupiedChildren
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:33:10.606962+00:00
-- url     : https://prove2.me/theorems/64faad83-4e37-51e6-a025-a2447fbb5e6c
-- title:
--   Oriented Branch: execute All Occupied Children
-- statement:
--   Execute every occupied genuine child in the audited order.  The resulting
--   configuration has accumulated exactly childMessageSum at the root, leaves the
--   external parent unchanged, and clears every non-root vertex of the branch.
--   Configuration-empty children are never tasks and remain untouched.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1154-L1273
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1154-L1273

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

theorem TreeStack.OrientedBranch.executeAllOccupiedChildren
    (B : OrientedBranch T) (C E : Configuration V)
    (hChildAttain :
      ∀ (c : B.Child) (E' : Configuration V) (d : ℤ) (q : ℕ),
        (B.childBranch c).Occupied E' →
        branchMessage E' (B.childBranch c) = some d →
        0 < (q : ℤ) + d →
        ∃ D : Configuration V,
          (B.childBranch c).ClearOutcome E' q D ∧
            (D B.root : ℤ) = (q : ℤ) + d)
    (hSame :
      ∀ v ∈ B.vertices, v ≠ B.root → E v = C v)
    (hSafe :
      TaskScheduleSafe
        (fun t : B.OccupiedChild C => t.gain)
        (E B.root : ℤ)
        (orderedTasks
          (fun t : B.OccupiedChild C => t.gain)
          (B.occupiedChildTasks C))) :
    ∃ D : Configuration V,
      B.BranchReach E D ∧
      (D B.root : ℤ) =
        (E B.root : ℤ) + childMessageSum C B ∧
      D B.parent = E B.parent ∧
      (∀ v ∈ B.vertices, v ≠ B.root → D v = 0) := by sorry
