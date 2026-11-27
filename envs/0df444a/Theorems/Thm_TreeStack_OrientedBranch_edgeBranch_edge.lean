-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_edgeBranch_edge
-- name    : TreeStack.OrientedBranch.edgeBranch_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:13:12.685898+00:00
-- url     : https://prove2.me/theorems/00e035ae-7fd8-5436-a533-410a30e2116d
-- title:
--   Oriented Branch: edge Branch edge
-- statement:
--   The Oriented Branch construction uses the edge Branch edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L44-L46
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L44-L46

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.edgeBranch_edge (e : T.graph.edgeFinset) :
    s((edgeBranch (T := T) e).root, (edgeBranch (T := T) e).parent) = e.1 := by sorry
