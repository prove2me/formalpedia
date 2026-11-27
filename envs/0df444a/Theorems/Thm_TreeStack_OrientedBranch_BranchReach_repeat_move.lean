-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_BranchReach_repeat_move
-- name    : TreeStack.OrientedBranch.BranchReach.repeat_move
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:27:30.15512+00:00
-- url     : https://prove2.me/theorems/734140ca-3af4-47e0-aa5e-77995834e351
-- title:
--   Branch Reach: repeat move
-- statement:
--   Repeating one legal oriented edge move a prescribed number of times
--   gives exact endpoint counts and leaves every other vertex unchanged.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L708-L754
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L708-L754

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

theorem TreeStack.OrientedBranch.BranchReach.repeat_move
    (B : OrientedBranch T) {u v : V}
    (huv : T.graph.Adj u v)
    (huCarrier : u ∈ B.carrier) (hvCarrier : v ∈ B.carrier) :
    ∀ (C : Configuration V) (n : ℕ),
      2 * n ≤ C u →
      ∃ D : Configuration V,
        B.BranchReach C D ∧
        D u = C u - 2 * n ∧
        D v = C v + n ∧
        (∀ w : V, w ≠ u → w ≠ v → D w = C w) := by sorry
