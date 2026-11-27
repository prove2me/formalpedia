-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_obstruction_branchMessage
-- name    : TreeStack.OrientedBranch.obstruction_branchMessage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:47:32.170573+00:00
-- url     : https://prove2.me/theorems/d4829191-2f13-4125-b28a-2c21a6b7527b
-- title:
--   Oriented Branch: obstruction branch Message
-- statement:
--   Every descendant branch of the selected root is occupied by the explicit
--   obstruction, and its exact recursive message is the negative obstruction
--   height.  The hypothesis says precisely that the selected root lies outside
--   the descendant-side component.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L654-L744
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Obstruction.lean#L654-L744

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch

theorem TreeStack.OrientedBranch.obstruction_branchMessage (r : V) (B : OrientedBranch T)
    (hAway : r ∉ B.vertices) :
    B.Occupied (obstruction T r) ∧
      branchMessage (obstruction T r) B =
        some (-(B.obstructionHeight : ℤ)) := by sorry
