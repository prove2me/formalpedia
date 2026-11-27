-- Prove2me | Theorems.Thm_TreeStack_RootTask_gain_eq_F
-- name    : TreeStack.RootTask.gain_eq_F
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:35:13.832064+00:00
-- url     : https://prove2.me/theorems/158e309a-33f2-54c2-a773-3c21a470ad0a
-- title:
--   Root Task: gain eq F
-- statement:
--   The Root Task construction uses the gain eq F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L228-L234
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L228-L234

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_gain_eq_F

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.RootTask.gain_eq_F
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) :
    t.gain = F (OrientedBranch.effectiveInput C t.branch) := by sorry
