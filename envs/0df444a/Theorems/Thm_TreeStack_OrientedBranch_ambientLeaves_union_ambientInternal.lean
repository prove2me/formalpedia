-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_ambientLeaves_union_ambientInternal
-- name    : TreeStack.OrientedBranch.ambientLeaves_union_ambientInternal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:36.022896+00:00
-- url     : https://prove2.me/theorems/1203bb51-6f13-4973-836e-a48eede98c03
-- title:
--   Oriented Branch: ambient Leaves union ambient Internal
-- statement:
--   In a nontrivial tree, every vertex is either a leaf or has degree greater
--   than one.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L232-L241
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L232-L241

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.ambientLeaves_union_ambientInternal [Nontrivial V] :
    ambientLeaves (T := T) ∪ ambientInternalVertices (T := T) =
      (Finset.univ : Finset V) := by sorry
