-- Prove2me | Theorems.Thm_TreeStack_nonstackable_mass_le_estim_sub_one
-- name    : TreeStack.nonstackable_mass_le_estim_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:27.218796+00:00
-- url     : https://prove2.me/theorems/e04e8d0e-78f4-5fd8-b19c-d75160b85ed2
-- title:
--   Tree Stack: nonstackable mass le estim sub one
-- statement:
--   Every globally non-stackable configuration lies below the estimator
--   threshold.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/UpperBound.lean#L138-L145
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/UpperBound.lean#L138-L145

import Mathlib
import Definitions.Def_TreeStack_Consolidation
import Definitions.Def_TreeStack_UpperBound
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.nonstackable_mass_le_estim_sub_one
    [Nontrivial V]
    (T : FiniteTree V) (C : Configuration V)
    (hNot : ¬ Stackable T.graph C) :
    mass C ≤ estim T - 1 := by sorry
