-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_stepMap_wayBelow
-- name    : Scott1972.ContinuousLattice.stepMap_wayBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:35:03.448501+00:00
-- url     : https://prove2.me/theorems/2a12b630-a1fd-534f-b1aa-7ab6a1909cfd
-- title:
--   Continuous Lattice: step Map way Below
-- statement:
--   **The step function is way below `f`.** If `e' ≪ f e`, then `ē[e, e'] ≪ f` in `[D → D']`,
--   witnessed by the Scott-open set `{g | e' ≪ g e}` (open because suprema in `[D → D']` are pointwise
--   and `{· ≪ ·}` is inaccessible by directed suprema).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L451-L466
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L451-L466

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem Scott1972.ContinuousLattice.stepMap_wayBelow {e : D} {e' : D'} {f : ScottMap D D'}
    (he' : e' ≪ (f : D → D') e) : stepMap e e' ≪ f := by sorry
