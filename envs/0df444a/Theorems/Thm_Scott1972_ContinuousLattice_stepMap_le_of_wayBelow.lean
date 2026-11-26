-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_stepMap_le_of_wayBelow
-- name    : Scott1972.ContinuousLattice.stepMap_le_of_wayBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:35:01.065891+00:00
-- url     : https://prove2.me/theorems/a1d5c6b5-07c1-5adc-b00c-37d260b60574
-- title:
--   Continuous Lattice: step Map le of way Below
-- statement:
--   If `e' ≪ g e` then the step function `ē[e, e']` lies below `g` (a pointwise argument).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L437-L446
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L437-L446

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

theorem Scott1972.ContinuousLattice.stepMap_le_of_wayBelow {e : D} {e' : D'} {g : ScottMap D D'}
    (h : e' ≪ (g : D → D') e) : stepMap e e' ≤ g := by sorry
