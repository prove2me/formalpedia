-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_child_nonempty_of_internal
-- name    : TreeStack.OrientedBranch.child_nonempty_of_internal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:49:26.529067+00:00
-- url     : https://prove2.me/theorems/c0f258a6-2fb6-5321-82a1-580b2c8fe1e0
-- title:
--   Oriented Branch: child nonempty of internal
-- statement:
--   An internal branch root has at least one genuine child.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L149-L164
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L149-L164

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.child_nonempty_of_internal (B : OrientedBranch T)
    (hInternal : 1 < T.graph.degree B.root) :
    Nonempty B.Child := by sorry
