-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_auxWeight_pos
-- name    : TreeStack.OrientedBranch.auxWeight_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:08:37.919343+00:00
-- url     : https://prove2.me/theorems/3783ea73-bd07-4b20-a47f-79fe5083fda0
-- title:
--   Oriented Branch: aux Weight pos
-- statement:
--   Auxiliary weights are positive (and in particular at least one).
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L436-L441
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Auxiliary.lean#L436-L441

import Mathlib
import Definitions.Def_TreeStack_DefectCharge
import Definitions.Def_TreeStack_Auxiliary
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.auxWeight_pos
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    0 < auxWeight C ambientRoot hScores v := by sorry
