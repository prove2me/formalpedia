-- Prove2me | Theorems.Thm_TreeStack_sum_root_obstructionHeight_eq_sigma_sub_one
-- name    : TreeStack.sum_root_obstructionHeight_eq_sigma_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:51:40.344672+00:00
-- url     : https://prove2.me/theorems/fa58f7a5-49bd-45a1-b6a9-0f89a77e0dea
-- title:
--   Tree Stack: sum root obstruction Height eq sigma sub one
-- statement:
--   The incident obstruction heights at a selected root sum to exactly
--   \`sigma T r - 1\`.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1200-L1236
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1200-L1236

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.sum_root_obstructionHeight_eq_sigma_sub_one
    (T : FiniteTree V) (r : V) :
    (∑ n : RootNeighbor T r, n.branch.obstructionHeight) =
      sigma T r - 1 := by sorry
