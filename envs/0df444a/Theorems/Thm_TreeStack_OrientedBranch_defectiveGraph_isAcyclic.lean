-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_defectiveGraph_isAcyclic
-- name    : TreeStack.OrientedBranch.defectiveGraph_isAcyclic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:03:29.482433+00:00
-- url     : https://prove2.me/theorems/bca2685e-b9ea-5cad-ab30-ff987bbc1f9d
-- title:
--   Oriented Branch: defective Graph is Acyclic
-- statement:
--   Defective retained edges form a forest: their graph is acyclic because it
--   is a subgraph of the ambient tree.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L39-L45
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/ForestOwner.lean#L39-L45

import Mathlib
import Definitions.Def_TreeStack_Support
import Definitions.Def_TreeStack_ForestOwner
set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.defectiveGraph_isAcyclic
    (C : Configuration V) :
    (defectiveGraph (T := T) C).IsAcyclic := by sorry
