-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_ambientLeaves_disjoint_ambientInternal
-- name    : TreeStack.OrientedBranch.ambientLeaves_disjoint_ambientInternal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:22.962133+00:00
-- url     : https://prove2.me/theorems/f714f2f7-5cb6-5a18-995a-96f1dc6b8cb7
-- title:
--   Oriented Branch: ambient Leaves disjoint ambient Internal
-- statement:
--   The Oriented Branch construction uses the ambient Leaves disjoint ambient Internal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L217-L228
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L217-L228

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.ambientLeaves_disjoint_ambientInternal :
    Disjoint
      (ambientLeaves (T := T))
      (ambientInternalVertices (T := T)) := by sorry
