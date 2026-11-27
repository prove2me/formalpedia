-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_exists_adj_mem_not_mem_of_nonempty_ne_univ
-- name    : TreeStack.OrientedBranch.exists_adj_mem_not_mem_of_nonempty_ne_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:55.315839+00:00
-- url     : https://prove2.me/theorems/c76cb73f-b648-5fb4-ba74-348e2355f1d5
-- title:
--   Oriented Branch: exists adj mem not mem of nonempty ne univ
-- statement:
--   Every nonempty proper finite vertex carrier in a connected tree has an
--   ambient edge crossing from the carrier to its complement.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L330-L358
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Consolidation.lean#L330-L358

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.exists_adj_mem_not_mem_of_nonempty_ne_univ
    (S : Finset V)
    (hNonempty : S.Nonempty)
    (hProper : S ≠ (Finset.univ : Finset V)) :
    ∃ a b : V, a ∈ S ∧ b ∉ S ∧ T.graph.Adj a b := by sorry
