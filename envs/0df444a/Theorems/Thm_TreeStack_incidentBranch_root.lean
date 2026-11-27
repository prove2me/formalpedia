-- Prove2me | Theorems.Thm_TreeStack_incidentBranch_root
-- name    : TreeStack.incidentBranch_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:37.266929+00:00
-- url     : https://prove2.me/theorems/226c435f-a886-5bfd-8a05-0cd6eb6cf77a
-- title:
--   Tree Stack: incident Branch root
-- statement:
--   The Tree Stack construction uses the incident Branch root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L17-L18
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean#L17-L18

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.incidentBranch_root (r u : V) (h : T.graph.Adj u r) :
    (incidentBranch T r u h).root = u := by sorry

attribute [defeq] TreeStack.incidentBranch_root
