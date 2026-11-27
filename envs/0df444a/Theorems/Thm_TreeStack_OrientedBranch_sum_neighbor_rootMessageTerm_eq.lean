-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_sum_neighbor_rootMessageTerm_eq
-- name    : TreeStack.OrientedBranch.sum_neighbor_rootMessageTerm_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:14:40.504739+00:00
-- url     : https://prove2.me/theorems/fb640079-9ca3-5285-8984-34f7c80b8c98
-- title:
--   Oriented Branch: sum neighbor root Message Term eq
-- statement:
--   A root message sum may be indexed only by genuine neighbors; all
--   nonneighbors already contribute zero by definition.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L280-L297
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L280-L297

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.sum_neighbor_rootMessageTerm_eq
    (C : Configuration V) (v : V) :
    (∑ u : T.graph.neighborSet v, rootMessageTerm T C v u) =
      rootMessageSum T C v := by sorry
