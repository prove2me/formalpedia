-- Prove2me | Theorems.Thm_TreeStack_stackableAt_iff_score_pos
-- name    : TreeStack.stackableAt_iff_score_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:35:45.457054+00:00
-- url     : https://prove2.me/theorems/44047106-286d-5035-b527-5f913ffe44e0
-- title:
--   Tree Stack: stackable At iff score pos
-- statement:
--   Exact rooted characterization: a configuration can be stacked at r
--   exactly when its recursive rooted score is positive.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L821-L827
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L821-L827

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.stackableAt_iff_score_pos
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    StackableAt T.graph C r ↔ 0 < score T C r := by sorry
