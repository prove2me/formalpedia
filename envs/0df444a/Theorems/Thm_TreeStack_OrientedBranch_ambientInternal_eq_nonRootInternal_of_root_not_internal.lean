-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_ambientInternal_eq_nonRootInternal_of_root_not_internal
-- name    : TreeStack.OrientedBranch.ambientInternal_eq_nonRootInternal_of_root_not_internal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:22.273566+00:00
-- url     : https://prove2.me/theorems/bc7d992b-19a5-5be9-9d2e-5657cf5dde21
-- title:
--   Oriented Branch: ambient Internal eq non Root Internal of root not internal
-- statement:
--   The Oriented Branch construction uses the ambient Internal eq non Root Internal of root not internal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L373-L383
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L373-L383

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.ambientInternal_eq_nonRootInternal_of_root_not_internal
    (T : FiniteTree V) (r : V)
    (hNotInternal : ¬ 1 < T.graph.degree r) :
    ambientInternalVertices (T := T) =
      nonRootInternalVertices T r := by sorry
