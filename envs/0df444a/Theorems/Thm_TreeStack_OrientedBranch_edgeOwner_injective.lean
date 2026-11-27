-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_edgeOwner_injective
-- name    : TreeStack.OrientedBranch.edgeOwner_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:13:20.310999+00:00
-- url     : https://prove2.me/theorems/f796037b-485c-5024-8a9a-3b3e4b8b010f
-- title:
--   Oriented Branch: edge Owner injective
-- statement:
--   Rooted owners are injective on all ambient tree edges.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L54-L62
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L54-L62

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.edgeOwner_injective (ambientRoot : V) :
    Function.Injective (edgeOwner (T := T) ambientRoot) := by sorry
