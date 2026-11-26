-- Prove2me | Theorems.Thm_TreeStack_rootEstimate_le_estim
-- name    : TreeStack.rootEstimate_le_estim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:29.186502+00:00
-- url     : https://prove2.me/theorems/1231e126-7686-5ba9-81c9-f8eba98cc125
-- title:
--   Tree Stack: root Estimate le estim
-- statement:
--   Every rooted estimator is bounded by the tree estimator.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L160-L164
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Estimator.lean#L160-L164

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Estimator
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical

theorem TreeStack.rootEstimate_le_estim {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    rootEstimate T r ≤ estim T := by sorry
