-- Prove2me | Theorems.Thm_TreeStack_obstruction_score_selected_root
-- name    : TreeStack.obstruction_score_selected_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:52:18.881222+00:00
-- url     : https://prove2.me/theorems/50b760ac-8537-417d-8896-f7b170e3f3c3
-- title:
--   Tree Stack: obstruction score selected root
-- statement:
--   At the selected root itself, the obstruction score is exactly zero.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1239-L1277
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1239-L1277

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.obstruction_score_selected_root
    (T : FiniteTree V) (r : V) :
    score T (obstruction T r) r = 0 := by sorry
