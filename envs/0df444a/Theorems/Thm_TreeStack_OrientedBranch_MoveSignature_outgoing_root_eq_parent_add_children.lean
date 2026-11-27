-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_MoveSignature_outgoing_root_eq_parent_add_children
-- name    : TreeStack.OrientedBranch.MoveSignature.outgoing_root_eq_parent_add_children
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:34:20.825793+00:00
-- url     : https://prove2.me/theorems/fa9ec3d5-f1cb-56b6-97ae-d01bf8b3efc7
-- title:
--   Move Signature: outgoing root eq parent add children
-- statement:
--   The Move Signature construction uses the outgoing root eq parent add children property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2033-L2073
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2033-L2073

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

theorem TreeStack.OrientedBranch.MoveSignature.outgoing_root_eq_parent_add_children
    (m : MoveSignature T) (B : OrientedBranch T) :
    (m.outgoing B.root : ℤ) =
      (m.count B.root B.parent : ℤ) +
        ∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            (m.count B.root v : ℤ)
          else
            0 := by sorry
