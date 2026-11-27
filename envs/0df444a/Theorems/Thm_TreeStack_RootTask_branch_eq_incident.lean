-- Prove2me | Theorems.Thm_TreeStack_RootTask_branch_eq_incident
-- name    : TreeStack.RootTask.branch_eq_incident
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:35:43.578066+00:00
-- url     : https://prove2.me/theorems/5fe100db-a4f7-4e2c-923d-35e30692c3dc
-- title:
--   Root Task: branch eq incident
-- statement:
--   The Root Task construction uses the branch eq incident property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L202-L209
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L202-L209

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.RootTask.branch_eq_incident
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) (h : T.graph.Adj t.1 r) :
    t.branch = incidentBranch T r t.1 h := by sorry
