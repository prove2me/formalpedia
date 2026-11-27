-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_exists_nat_three_loss
-- name    : TreeStack.OrientedBranch.exists_nat_three_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:34:36.865498+00:00
-- url     : https://prove2.me/theorems/802eb056-412e-5263-8d80-ae2c9f646777
-- title:
--   Oriented Branch: exists nat three loss
-- statement:
--   If a is no larger than b and the two integers have the same residue
--   modulo three, then a is exactly b minus three times a natural number.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2125-L2138
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Boundary.lean#L2125-L2138

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

theorem TreeStack.OrientedBranch.exists_nat_three_loss {a b : ℤ}
    (hle : a ≤ b) (hmod : a % 3 = b % 3) :
    ∃ k : ℕ, a = b - 3 * (k : ℤ) := by sorry
