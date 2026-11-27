-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_BranchReach_exists_moveSignature
-- name    : TreeStack.OrientedBranch.BranchReach.exists_moveSignature
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:27:06.406382+00:00
-- url     : https://prove2.me/theorems/75c54399-ab0b-437c-9c3e-5a96f56a30a1
-- title:
--   Branch Reach: exists move Signature
-- statement:
--   A branch-local reachability proof has an exact oriented move-count
--   signature.  The final clause is causal on every oriented subbranch contained
--   in the ambient branch: if no outward boundary move of that subbranch occurs,
--   initial occupancy of the subbranch persists.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1534-L1599
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1534-L1599

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

theorem TreeStack.OrientedBranch.BranchReach.exists_moveSignature
    (B : OrientedBranch T) {C D : Configuration V}
    (hreach : B.BranchReach C D) :
    ∃ m : MoveSignature T,
      MoveSignature.SupportedOn m B ∧
      (∀ w : V,
        (D w : ℤ) =
          (C w : ℤ) + (m.incoming w : ℤ) -
            2 * (m.outgoing w : ℤ)) ∧
      (∀ A : OrientedBranch T,
        A.vertices ⊆ B.vertices →
        A.Occupied C →
        m.count A.root A.parent = 0 →
        A.Occupied D) := by sorry
