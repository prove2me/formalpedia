-- Prove2me | Theorems.Thm_TreeStack_mass_le_estim_sub_one_of_all_scores_nonpos
-- name    : TreeStack.mass_le_estim_sub_one_of_all_scores_nonpos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:58.413927+00:00
-- url     : https://prove2.me/theorems/c122892f-98ff-4d4c-9775-c9ab4709e66e
-- title:
--   Tree Stack: mass le estim sub one of all scores nonpos
-- statement:
--   Natural-subtraction form of the arbitrary-defect estimator bound.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/UpperBound.lean#L127-L134
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/UpperBound.lean#L127-L134

import Mathlib
import Definitions.Def_TreeStack_Consolidation
import Definitions.Def_TreeStack_UpperBound
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.mass_le_estim_sub_one_of_all_scores_nonpos
    [Nontrivial V]
    (T : FiniteTree V) (C : Configuration V)
    (hScores : ∀ v, score T C v ≤ 0) :
    mass C ≤ estim T - 1 := by sorry
