-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_adj_neg
-- name    : TreeStack.OrientedBranch.boundaryParityWeight_adj_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:33:46.094478+00:00
-- url     : https://prove2.me/theorems/1830a6f0-c991-4537-9148-b3269201ac07
-- title:
--   Oriented Branch: boundary Parity Weight adj neg
-- statement:
--   The Oriented Branch construction uses the boundary Parity Weight adj neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1783-L1809
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L1783-L1809

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

theorem TreeStack.OrientedBranch.boundaryParityWeight_adj_neg (B : OrientedBranch T)
    {u v : V} (huv : T.graph.Adj u v) :
    B.boundaryParityWeight v = -B.boundaryParityWeight u := by sorry
