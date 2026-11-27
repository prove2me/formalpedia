-- Prove2me | Theorems.Thm_TreeStack_obstruction_apply_ne
-- name    : TreeStack.obstruction_apply_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:46:48.691826+00:00
-- url     : https://prove2.me/theorems/a9b15f9d-3cc7-4afa-a360-ea0630d8727e
-- title:
--   Tree Stack: obstruction apply ne
-- statement:
--   The Tree Stack construction uses the obstruction apply ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L27-L30
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L27-L30

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.obstruction_apply_ne (T : FiniteTree V) (r v : V) (hvr : v ≠ r) :
    obstruction T r v = if T.graph.degree v = 1 then 1 else 0 := by sorry
