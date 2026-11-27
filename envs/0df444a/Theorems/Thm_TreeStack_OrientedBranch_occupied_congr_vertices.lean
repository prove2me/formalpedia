-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_occupied_congr_vertices
-- name    : TreeStack.OrientedBranch.occupied_congr_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:27:33.52536+00:00
-- url     : https://prove2.me/theorems/454a38a1-f60a-5dee-8af7-ed556f58e01f
-- title:
--   Oriented Branch: occupied congr vertices
-- statement:
--   The Oriented Branch construction uses the occupied congr vertices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L463-L475
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L463-L475

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.occupied_congr_vertices
    (B : OrientedBranch T) (C D : Configuration V)
    (hCD : ∀ v ∈ B.vertices, C v = D v) :
    B.Occupied C ↔ B.Occupied D := by sorry
