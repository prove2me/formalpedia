-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_occupied_or_reverse_occupied
-- name    : TreeStack.OrientedBranch.occupied_or_reverse_occupied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:53:03.121948+00:00
-- url     : https://prove2.me/theorems/842d2922-c8d8-5693-871b-1951d719254c
-- title:
--   Oriented Branch: occupied or reverse occupied
-- statement:
--   At least one edge side is occupied as soon as the configuration has a
--   positive pile somewhere.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L78-L84
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Support.lean#L78-L84

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.occupied_or_reverse_occupied
    (C : Configuration V) (B : OrientedBranch T)
    {x : V} (hx : 0 < C x) :
    B.Occupied C ∨ B.reverseBranch.Occupied C := by sorry
