-- Prove2me | Theorems.Thm_TreeStack_RootTask_branch_root
-- name    : TreeStack.RootTask.branch_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:37.810565+00:00
-- url     : https://prove2.me/theorems/e398edb9-0b79-5478-9a36-6eb703a7bedd
-- title:
--   Root Task: branch root
-- statement:
--   The Root Task construction uses the branch root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L211-L214
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L211-L214

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.RootTask.branch_root
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) :
    t.branch.root = t.1 := by sorry

attribute [defeq] TreeStack.RootTask.branch_root
