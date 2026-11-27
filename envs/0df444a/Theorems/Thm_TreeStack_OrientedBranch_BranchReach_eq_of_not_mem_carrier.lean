-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_BranchReach_eq_of_not_mem_carrier
-- name    : TreeStack.OrientedBranch.BranchReach.eq_of_not_mem_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:07.453254+00:00
-- url     : https://prove2.me/theorems/98fecb42-b109-58ce-ad45-9d545db85610
-- title:
--   Branch Reach: eq of not mem carrier
-- statement:
--   A branch-local legal sequence cannot alter a vertex outside its carrier.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L669-L686
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L669-L686

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

theorem TreeStack.OrientedBranch.BranchReach.eq_of_not_mem_carrier
    (B : OrientedBranch T) {C D : Configuration V}
    (hreach : B.BranchReach C D) {w : V}
    (hw : w ∉ B.carrier) :
    D w = C w := by sorry
