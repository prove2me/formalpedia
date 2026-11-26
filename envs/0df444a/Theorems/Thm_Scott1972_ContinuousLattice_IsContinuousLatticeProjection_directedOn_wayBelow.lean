-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeProjection_directedOn_wayBelow
-- name    : Scott1972.ContinuousLattice.IsContinuousLatticeProjection.directedOn_wayBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:39:53.644325+00:00
-- url     : https://prove2.me/theorems/4c37f958-db39-48fa-b590-287ce3b160a9
-- title:
--   Is Continuous Lattice Projection: directed On way Below
-- statement:
--   The Is Continuous Lattice Projection construction uses the directed On way Below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1112-L1114
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1112-L1114

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_directedOn_wayBelow

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
open Finset
open Scott1972.ContinuousLattice.IsContinuousLatticeProjection

theorem Scott1972.ContinuousLattice.IsContinuousLatticeProjection.directedOn_wayBelow (a : D) : DirectedOn (· ≤ ·) { z | z ≪ a } := by sorry
