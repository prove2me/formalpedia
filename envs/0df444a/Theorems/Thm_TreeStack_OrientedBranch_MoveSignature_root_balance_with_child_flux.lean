-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_MoveSignature_root_balance_with_child_flux
-- name    : TreeStack.OrientedBranch.MoveSignature.root_balance_with_child_flux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:34:29.382507+00:00
-- url     : https://prove2.me/theorems/d04f8f3e-0ca9-594e-9971-9a84798605cd
-- title:
--   Move Signature: root balance with child flux
-- statement:
--   The clearing balance at the branch root, separated into the external
--   boundary edge and the total flux of genuine child branches.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2110-L2121
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2110-L2121

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

theorem TreeStack.OrientedBranch.MoveSignature.root_balance_with_child_flux
    (m : MoveSignature T) (C : Configuration V) (B : OrientedBranch T)
    (hbal : m.BalancesAt C B.root) :
    (C B.root : ℤ) + signatureChildFluxSum m B +
        (m.count B.parent B.root : ℤ) -
      2 * (m.count B.root B.parent : ℤ) = 0 := by sorry
