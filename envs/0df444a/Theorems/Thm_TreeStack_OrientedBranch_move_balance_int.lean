-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_move_balance_int
-- name    : TreeStack.OrientedBranch.move_balance_int
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:27:58.935662+00:00
-- url     : https://prove2.me/theorems/e6066a43-c7bd-529a-a8af-b15cefdf84c8
-- title:
--   Oriented Branch: move balance int
-- statement:
--   Exact pointwise integer accounting for one legal move.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1516-L1528
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1516-L1528

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

theorem TreeStack.OrientedBranch.move_balance_int (C : Configuration V) {u v : V}
    (huv : u ≠ v) (hu : 2 ≤ C u) (w : V) :
    (move C u v w : ℤ) =
      (C w : ℤ) + (if w = v then 1 else 0) -
        2 * (if w = u then 1 else 0) := by sorry
