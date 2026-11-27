-- Prove2me | Theorems.Thm_TreeStack_stackableAt_of_score_pos
-- name    : TreeStack.stackableAt_of_score_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:35:40.797146+00:00
-- url     : https://prove2.me/theorems/50fef8f7-3512-4909-b4de-78d3a8aeeda4
-- title:
--   Tree Stack: stackable At of score pos
-- statement:
--   Positive rooted score gives an explicit legal stack at the chosen root.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L597-L622
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L597-L622

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.stackableAt_of_score_pos
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (hScore : 0 < score T C r) :
    StackableAt T.graph C r := by sorry
