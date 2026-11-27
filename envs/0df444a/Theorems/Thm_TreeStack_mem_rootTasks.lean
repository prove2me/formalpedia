-- Prove2me | Theorems.Thm_TreeStack_mem_rootTasks
-- name    : TreeStack.mem_rootTasks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:31:18.582399+00:00
-- url     : https://prove2.me/theorems/e9adc298-9143-4692-8afa-eec6426a6a61
-- title:
--   Tree Stack: mem root Tasks
-- statement:
--   The Tree Stack construction uses the mem root Tasks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L269-L274
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L269-L274

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.mem_rootTasks
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (t : RootTask T C r) :
    t ∈ rootTasks T C r := by sorry
