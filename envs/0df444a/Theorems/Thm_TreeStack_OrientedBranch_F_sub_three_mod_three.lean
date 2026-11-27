-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_F_sub_three_mod_three
-- name    : TreeStack.OrientedBranch.F_sub_three_mod_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:34:40.649061+00:00
-- url     : https://prove2.me/theorems/4b1230f2-8036-5bdd-a135-87da184753ef
-- title:
--   Oriented Branch: F sub three mod three
-- statement:
--   The transfer keeps the same residue modulo three when its input is
--   lowered by three.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2142-L2145
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2142-L2145

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]

theorem TreeStack.OrientedBranch.F_sub_three_mod_three (z : ℤ) :
    F (z - 3) % 3 = F z % 3 := by sorry
