-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_attainRootTransfer_even
-- name    : TreeStack.OrientedBranch.attainRootTransfer_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:27:57.890541+00:00
-- url     : https://prove2.me/theorems/436faf40-1b00-4ccb-b6f0-2213f8c36cac
-- title:
--   Oriented Branch: attain Root Transfer even
-- statement:
--   Once all non-root branch vertices are clear, an even root pile 2k
--   with k at least one is cleared optimally by k outward boundary moves.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1277-L1322
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1277-L1322

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

theorem TreeStack.OrientedBranch.attainRootTransfer_even
    (B : OrientedBranch T) (E : Configuration V) (k : ℕ)
    (hk : 1 ≤ k)
    (hRoot : E B.root = 2 * k)
    (hNonroot :
      ∀ v ∈ B.vertices, v ≠ B.root → E v = 0) :
    ∃ D : Configuration V,
      B.BranchReach E D ∧
      B.Cleared D ∧
      (D B.parent : ℤ) =
        (E B.parent : ℤ) + F (E B.root : ℤ) := by sorry
