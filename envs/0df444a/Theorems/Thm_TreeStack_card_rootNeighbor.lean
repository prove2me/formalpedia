-- Prove2me | Theorems.Thm_TreeStack_card_rootNeighbor
-- name    : TreeStack.card_rootNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:51:23.16977+00:00
-- url     : https://prove2.me/theorems/38384ecd-6335-516e-bac5-587bcf9e7d92
-- title:
--   Tree Stack: card root Neighbor
-- statement:
--   The number of root neighbors is the degree of the root.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1104-L1118
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1104-L1118

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.card_rootNeighbor (T : FiniteTree V) (r : V) :
    Fintype.card (RootNeighbor T r) = T.graph.degree r := by sorry
