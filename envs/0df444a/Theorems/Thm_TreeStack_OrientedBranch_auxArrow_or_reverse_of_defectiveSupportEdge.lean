-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxArrow_or_reverse_of_defectiveSupportEdge
-- name    : TreeStack.OrientedBranch.auxArrow_or_reverse_of_defectiveSupportEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:07:18.578008+00:00
-- url     : https://prove2.me/theorems/49ce36c6-f270-5be1-81f3-4b43170173da
-- title:
--   Oriented Branch: aux Arrow or reverse of defective Support Edge
-- statement:
--   Every defective retained support edge receives an auxiliary direction.
--   Oriented-type edges use their forced message direction; two-negative edges
--   point toward the fixed rooted owner.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L116-L178
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L116-L178

import Mathlib
import Definitions.Def_TreeStack_DefectCharge
import Definitions.Def_TreeStack_Auxiliary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxArrow_or_reverse_of_defectiveSupportEdge
    (C : Configuration V) (ambientRoot : V) (B : OrientedBranch T)
    (hDef : B.DefectiveSupportEdge C) :
    AuxArrow (T := T) C ambientRoot B.root B.parent ∨
      AuxArrow (T := T) C ambientRoot B.parent B.root := by sorry
