-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_ambientInternal_eq_insert_nonRootInternal_of_root_internal
-- name    : TreeStack.OrientedBranch.ambientInternal_eq_insert_nonRootInternal_of_root_internal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:20.936261+00:00
-- url     : https://prove2.me/theorems/815e74e1-3084-49b8-8c08-aceb46a15066
-- title:
--   Oriented Branch: ambient Internal eq insert non Root Internal of root internal
-- statement:
--   The Oriented Branch construction uses the ambient Internal eq insert non Root Internal of root internal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L385-L395
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L385-L395

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.ambientInternal_eq_insert_nonRootInternal_of_root_internal
    (T : FiniteTree V) (r : V)
    (hInternal : 1 < T.graph.degree r) :
    ambientInternalVertices (T := T) =
      insert r (nonRootInternalVertices T r) := by sorry
