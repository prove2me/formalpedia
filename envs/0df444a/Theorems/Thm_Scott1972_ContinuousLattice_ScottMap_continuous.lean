-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_ScottMap_continuous
-- name    : Scott1972.ContinuousLattice.ScottMap.continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:34:52.659897+00:00
-- url     : https://prove2.me/theorems/5bf4d50a-0148-4a34-9fba-093e396d5f76
-- title:
--   Scott Map: continuous
-- statement:
--   The Scott Map construction uses the continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L151-L153
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L151-L153

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
open Scott1972.ContinuousLattice.ScottMap

theorem Scott1972.ContinuousLattice.ScottMap.continuous (f : ScottMap D D') :
    @Continuous D D' scottTopologicalSpace scottTopologicalSpace f := by sorry
