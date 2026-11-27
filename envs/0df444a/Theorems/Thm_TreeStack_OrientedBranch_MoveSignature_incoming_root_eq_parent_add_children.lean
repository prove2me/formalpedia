-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_MoveSignature_incoming_root_eq_parent_add_children
-- name    : TreeStack.OrientedBranch.MoveSignature.incoming_root_eq_parent_add_children
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:34:16.761647+00:00
-- url     : https://prove2.me/theorems/b3e0e2ff-3b59-553f-9f0d-722601dfd1ef
-- title:
--   Move Signature: incoming root eq parent add children
-- statement:
--   The Move Signature construction uses the incoming root eq parent add children property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1991-L2031
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1991-L2031

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

theorem TreeStack.OrientedBranch.MoveSignature.incoming_root_eq_parent_add_children
    (m : MoveSignature T) (B : OrientedBranch T) :
    (m.incoming B.root : ℤ) =
      (m.count B.parent B.root : ℤ) +
        ∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            (m.count v B.root : ℤ)
          else
            0 := by sorry
