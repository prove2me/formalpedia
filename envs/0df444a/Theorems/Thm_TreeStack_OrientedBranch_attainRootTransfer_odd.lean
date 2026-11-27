-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_attainRootTransfer_odd
-- name    : TreeStack.OrientedBranch.attainRootTransfer_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:33:03.030867+00:00
-- url     : https://prove2.me/theorems/61b8cf55-aadf-5c7c-b92c-38473ac6eda5
-- title:
--   Oriented Branch: attain Root Transfer odd
-- statement:
--   Once all non-root branch vertices are clear, an odd root pile 2k+1
--   with k at least one attains the exact transfer by an explicit legal sequence.
--   If the boundary is empty, two outward moves are made first; otherwise one
--   outward move suffices to fund the single inward move.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1328-L1466
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1328-L1466

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

theorem TreeStack.OrientedBranch.attainRootTransfer_odd
    (B : OrientedBranch T) (E : Configuration V) (k : ℕ)
    (hk : 1 ≤ k)
    (hRoot : E B.root = 2 * k + 1)
    (hNonroot :
      ∀ v ∈ B.vertices, v ≠ B.root → E v = 0)
    (hPos :
      0 < (E B.parent : ℤ) + F (E B.root : ℤ)) :
    ∃ D : Configuration V,
      B.BranchReach E D ∧
      B.Cleared D ∧
      (D B.parent : ℤ) =
        (E B.parent : ℤ) + F (E B.root : ℤ) := by sorry
