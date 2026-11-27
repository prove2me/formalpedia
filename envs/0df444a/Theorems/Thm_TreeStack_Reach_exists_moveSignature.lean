-- Prove2me | Theorems.Thm_TreeStack_Reach_exists_moveSignature
-- name    : TreeStack.Reach.exists_moveSignature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:47:34.67522+00:00
-- url     : https://prove2.me/theorems/06d8c3ef-4aa9-51e5-8d0d-d020c2551303
-- title:
--   Reach: exists move Signature
-- statement:
--   A global legal reach has an exact move-count signature.  Moreover, if an
--   oriented branch starts occupied and its outward boundary count is zero, then
--   that branch remains occupied.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L627-L689
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L627-L689

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
import Theorems.Thm_TreeStack_OrientedBranch_BranchReach_exists_moveSignature

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.Reach.exists_moveSignature
    [DecidableEq V] {C D : Configuration V}
    (hreach : Reach T.graph C D) :
    ∃ m : MoveSignature T,
      (∀ w : V,
        (D w : ℤ) =
          (C w : ℤ) + (m.incoming w : ℤ) -
            2 * (m.outgoing w : ℤ)) ∧
      (∀ A : OrientedBranch T,
        A.Occupied C →
        m.count A.root A.parent = 0 →
        A.Occupied D) := by sorry
