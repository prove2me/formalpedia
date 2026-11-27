-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_attainRootTransfer_ge_two
-- name    : TreeStack.OrientedBranch.attainRootTransfer_ge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:33:52.341317+00:00
-- url     : https://prove2.me/theorems/4e3a18e3-44bb-4f15-9e8e-3d87868ef8c8
-- title:
--   Oriented Branch: attain Root Transfer ge two
-- statement:
--   Root/boundary attainment for every effective root pile at least two.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1469-L1496
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1469-L1496

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

theorem TreeStack.OrientedBranch.attainRootTransfer_ge_two
    (B : OrientedBranch T) (E : Configuration V)
    (hRootTwo : 2 ≤ E B.root)
    (hNonroot :
      ∀ v ∈ B.vertices, v ≠ B.root → E v = 0)
    (hPos :
      0 < (E B.parent : ℤ) + F (E B.root : ℤ)) :
    ∃ D : Configuration V,
      B.BranchReach E D ∧
      B.Cleared D ∧
      (D B.parent : ℤ) =
        (E B.parent : ℤ) + F (E B.root : ℤ) := by sorry
