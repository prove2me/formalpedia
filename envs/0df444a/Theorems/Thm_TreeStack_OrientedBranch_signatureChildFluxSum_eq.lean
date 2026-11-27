-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_signatureChildFluxSum_eq
-- name    : TreeStack.OrientedBranch.signatureChildFluxSum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:34:40.680783+00:00
-- url     : https://prove2.me/theorems/753d3a6c-beb1-4a2d-8b17-48cdf968364f
-- title:
--   Oriented Branch: signature Child Flux Sum eq
-- statement:
--   The Oriented Branch construction uses the signature Child Flux Sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2075-L2106
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2075-L2106

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

theorem TreeStack.OrientedBranch.signatureChildFluxSum_eq
    (m : MoveSignature T) (B : OrientedBranch T) :
    signatureChildFluxSum m B =
      (∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          (m.count v B.root : ℤ)
        else
          0) -
      2 * (∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          (m.count B.root v : ℤ)
        else
          0) := by sorry
