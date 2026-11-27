-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_rootEstimate_eq_one_add_ambientLeafCount_add_rootedInternalPotential
-- name    : TreeStack.OrientedBranch.rootEstimate_eq_one_add_ambientLeafCount_add_rootedInternalPotential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:24.821801+00:00
-- url     : https://prove2.me/theorems/7a739ec8-68aa-5cec-bbf6-76bb6efecc76
-- title:
--   Oriented Branch: root Estimate eq one add ambient Leaf Count add rooted Internal Potential
-- statement:
--   Root-insensitive decomposition of the rooted estimator.  This statement
--   handles degree-one roots explicitly: the root term in `sigma` exactly replaces
--   the leaf omitted from `leafCount T r`.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L400-L453
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/LeafSlack.lean#L400-L453

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.rootEstimate_eq_one_add_ambientLeafCount_add_rootedInternalPotential
    [Nontrivial V] (T : FiniteTree V) (r : V) :
    rootEstimate T r =
      1 + ambientLeafCount (T := T) + rootedInternalPotential T r := by sorry
