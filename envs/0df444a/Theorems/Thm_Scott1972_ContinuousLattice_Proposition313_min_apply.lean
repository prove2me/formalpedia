-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_Proposition313_min_apply
-- name    : Scott1972.ContinuousLattice.Proposition313.min_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:35:02.183481+00:00
-- url     : https://prove2.me/theorems/416fc466-833a-4ce1-b101-6993354a3b41
-- title:
--   Proposition313: min apply
-- statement:
--   The Proposition313 construction uses the min apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1643-L1643
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1643-L1643

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
open Scott1972.ContinuousLattice.Proposition313

theorem Scott1972.ContinuousLattice.Proposition313.min_apply (f : ScottMap D D) : (min f : D) = (f : D → D) ⊥ := by sorry

attribute [defeq] Scott1972.ContinuousLattice.Proposition313.min_apply
