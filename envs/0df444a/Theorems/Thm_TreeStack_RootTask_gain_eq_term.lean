-- Prove2me | Theorems.Thm_TreeStack_RootTask_gain_eq_term
-- name    : TreeStack.RootTask.gain_eq_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:42:10.993139+00:00
-- url     : https://prove2.me/theorems/44ed1749-5e70-54b4-9e27-d930cac33833
-- title:
--   Root Task: gain eq term
-- statement:
--   The Root Task construction uses the gain eq term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L249-L254
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L249-L254

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_gain_eq_term

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.RootTask.gain_eq_term
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) :
    t.gain = rootMessageTerm T C r t.1 := by sorry
