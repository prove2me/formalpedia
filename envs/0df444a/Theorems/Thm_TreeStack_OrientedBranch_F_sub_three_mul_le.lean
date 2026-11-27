-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_F_sub_three_mul_le
-- name    : TreeStack.OrientedBranch.F_sub_three_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:34:46.355975+00:00
-- url     : https://prove2.me/theorems/5841c10b-2b28-530a-8fc2-2e574e5c8eaa
-- title:
--   Oriented Branch: F sub three mul le
-- statement:
--   Iterated form of the three-step transfer inequality.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2148-L2161
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2148-L2161

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

theorem TreeStack.OrientedBranch.F_sub_three_mul_le (z : ℤ) :
    ∀ k : ℕ, F (z - 3 * (k : ℤ)) ≤ F z
  := by sorry
