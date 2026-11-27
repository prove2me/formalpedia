-- Prove2me | Theorems.Thm_TreeStack_score_pos_of_stackableAt
-- name    : TreeStack.score_pos_of_stackableAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:36:25.547735+00:00
-- url     : https://prove2.me/theorems/ef1c8a1b-3db3-4096-92cc-424b7d66cacf
-- title:
--   Tree Stack: score pos of stackable At
-- statement:
--   Any legal stack at r forces the rooted score to be positive.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L709-L817
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L709-L817

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.score_pos_of_stackableAt
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (hStackable : StackableAt T.graph C r) :
    0 < score T C r := by sorry
