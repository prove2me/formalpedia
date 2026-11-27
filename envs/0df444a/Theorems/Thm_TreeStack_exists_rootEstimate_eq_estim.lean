-- Prove2me | Theorems.Thm_TreeStack_exists_rootEstimate_eq_estim
-- name    : TreeStack.exists_rootEstimate_eq_estim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:52:44.506312+00:00
-- url     : https://prove2.me/theorems/bde59603-dac9-4e43-a8cc-65ccaae826e1
-- title:
--   Tree Stack: exists root Estimate eq estim
-- statement:
--   The finite maximum defining the estimator is attained by some root.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1348-L1361
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1348-L1361

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.exists_rootEstimate_eq_estim
    (T : FiniteTree V) :
    ∃ r : V, rootEstimate T r = estim T := by sorry
