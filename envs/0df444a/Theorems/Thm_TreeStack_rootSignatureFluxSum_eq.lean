-- Prove2me | Theorems.Thm_TreeStack_rootSignatureFluxSum_eq
-- name    : TreeStack.rootSignatureFluxSum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:36:27.706036+00:00
-- url     : https://prove2.me/theorems/ed66a0bb-d98c-4c2e-b10d-fcf7344b5b91
-- title:
--   Tree Stack: root Signature Flux Sum eq
-- statement:
--   The Tree Stack construction uses the root Signature Flux Sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L700-L706
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L700-L706

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.rootSignatureFluxSum_eq
    (m : MoveSignature T) (r : V) :
    rootSignatureFluxSum m r =
      (m.incoming r : ℤ) - 2 * (m.outgoing r : ℤ) := by sorry
