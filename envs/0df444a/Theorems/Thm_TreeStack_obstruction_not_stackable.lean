-- Prove2me | Theorems.Thm_TreeStack_obstruction_not_stackable
-- name    : TreeStack.obstruction_not_stackable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:52:08.102803+00:00
-- url     : https://prove2.me/theorems/fe3616e8-6924-593b-bcb4-7034a5587c02
-- title:
--   Tree Stack: obstruction not stackable
-- statement:
--   The explicit obstruction is globally non-stackable.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1337-L1345
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L1337-L1345

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.obstruction_not_stackable
    (T : FiniteTree V) (r : V) :
    ¬ Stackable T.graph (obstruction T r) := by sorry
