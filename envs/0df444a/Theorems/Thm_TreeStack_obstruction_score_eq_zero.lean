-- Prove2me | Theorems.Thm_TreeStack_obstruction_score_eq_zero
-- name    : TreeStack.obstruction_score_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:52:00.023264+00:00
-- url     : https://prove2.me/theorems/bda5d7d2-e901-400c-a0fc-010aca95bae4
-- title:
--   Tree Stack: obstruction score eq zero
-- statement:
--   Every rooted score of the explicit estimator obstruction is exactly zero.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1316-L1334
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1316-L1334

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.obstruction_score_eq_zero
    (T : FiniteTree V) (r v : V) :
    score T (obstruction T r) v = 0 := by sorry
