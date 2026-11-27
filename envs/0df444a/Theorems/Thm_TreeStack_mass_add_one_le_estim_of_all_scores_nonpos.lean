-- Prove2me | Theorems.Thm_TreeStack_mass_add_one_le_estim_of_all_scores_nonpos
-- name    : TreeStack.mass_add_one_le_estim_of_all_scores_nonpos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:34.996659+00:00
-- url     : https://prove2.me/theorems/c37e6dd4-9e1c-4f35-afb3-350fe83f1f2a
-- title:
--   Tree Stack: mass add one le estim of all scores nonpos
-- statement:
--   The arbitrary-defect upper bound in additive form.  If every rooted score
--   is nonpositive, then the configuration has at most `estim T - 1` pebbles.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/UpperBound.lean#L97-L124
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/UpperBound.lean#L97-L124

import Mathlib
import Definitions.Def_TreeStack_Consolidation
import Definitions.Def_TreeStack_UpperBound
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.mass_add_one_le_estim_of_all_scores_nonpos
    [Nontrivial V]
    (T : FiniteTree V) (C : Configuration V)
    (hScores : ∀ v, score T C v ≤ 0) :
    mass C + 1 ≤ estim T := by sorry
