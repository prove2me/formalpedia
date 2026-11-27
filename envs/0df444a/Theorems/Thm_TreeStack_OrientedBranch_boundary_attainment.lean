-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_boundary_attainment
-- name    : TreeStack.OrientedBranch.boundary_attainment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:22.440032+00:00
-- url     : https://prove2.me/theorems/17ced3b4-3ca6-44e1-8386-4f417cbb19ba
-- title:
--   Oriented Branch: boundary attainment
-- statement:
--   Constructive half of the exact boundary invariant.  For every occupied
--   branch, whenever the requested final boundary value q+d is positive, there is
--   a legal branch-local clearing that attains it exactly.  The recursion is on
--   strict child-branch cardinality.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2455-L2647
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2455-L2647

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

theorem TreeStack.OrientedBranch.boundary_attainment
    (C : Configuration V) (B : OrientedBranch T)
    (hOcc : B.Occupied C) :
    ∀ d : ℤ, branchMessage C B = some d →
      ∀ q : ℕ, 0 < (q : ℤ) + d →
        ∃ D : Configuration V,
          B.ClearOutcome C q D ∧
            (D B.parent : ℤ) = (q : ℤ) + d := by sorry
