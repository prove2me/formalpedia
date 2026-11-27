-- Prove2me | Theorems.Thm_TreeStack_OrientedBranch_sum_dart_eq_sum_edge_pair
-- name    : TreeStack.OrientedBranch.sum_dart_eq_sum_edge_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:13:32.498308+00:00
-- url     : https://prove2.me/theorems/d33251e9-fc8e-46fa-af78-3445a13cf01b
-- title:
--   Oriented Branch: sum dart eq sum edge pair
-- statement:
--   Sum a dart function by grouping the two orientations of each undirected
--   edge.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L252-L267
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/GlobalCharge.lean#L252-L267

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}

theorem TreeStack.OrientedBranch.sum_dart_eq_sum_edge_pair (f : T.graph.Dart → ℤ) :
    (∑ d : T.graph.Dart, f d) =
      ∑ e : T.graph.edgeFinset,
        (f (edgeDart (T := T) e) + f (edgeDart (T := T) e).symm) := by sorry
