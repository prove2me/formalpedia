-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_defectiveGraph_le_tree
-- name    : TreeStack.OrientedBranch.defectiveGraph_le_tree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:56:56.045802+00:00
-- url     : https://prove2.me/theorems/b4813a30-5d1b-5f76-825e-d4db40c587b9
-- title:
--   Oriented Branch: defective Graph le tree
-- statement:
--   The defective-edge graph is a spanning subgraph of the ambient tree.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L30-L35
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L30-L35

import Mathlib
import Definitions.Def_TreeStack_Support
import Definitions.Def_TreeStack_ForestOwner
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.defectiveGraph_le_tree
    (C : Configuration V) :
    defectiveGraph (T := T) C ≤ T.graph := by sorry
