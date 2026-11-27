-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_MoveSignature_zero_supportedOn
-- name    : TreeStack.OrientedBranch.MoveSignature.zero_supportedOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:33:13.898283+00:00
-- url     : https://prove2.me/theorems/d46edb56-2a35-5a58-892b-2e8c1f028fcc
-- title:
--   Move Signature: zero supported On
-- statement:
--   The Move Signature construction uses the zero supported On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1498-L1501
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1498-L1501

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

theorem TreeStack.OrientedBranch.MoveSignature.zero_supportedOn (B : OrientedBranch T) :
    MoveSignature.SupportedOn (MoveSignature.zero T) B := by sorry
