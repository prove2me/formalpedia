-- Prove2me | Theorems.Thm_TreeStack_RootTask_branch_parent
-- name    : TreeStack.RootTask.branch_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:45.795123+00:00
-- url     : https://prove2.me/theorems/af1ec983-480b-40d1-925f-0d94ba03c895
-- title:
--   Root Task: branch parent
-- statement:
--   The Root Task construction uses the branch parent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L216-L219
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L216-L219

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.RootTask.branch_parent
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) :
    t.branch.parent = r := by sorry

attribute [defeq] TreeStack.RootTask.branch_parent
