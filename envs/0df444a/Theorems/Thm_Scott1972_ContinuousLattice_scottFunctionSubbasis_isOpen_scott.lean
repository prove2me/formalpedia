-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottFunctionSubbasis_isOpen_scott
-- name    : Scott1972.ContinuousLattice.scottFunctionSubbasis_isOpen_scott
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:36:22.411073+00:00
-- url     : https://prove2.me/theorems/220daeeb-11ec-4b92-bdcd-036c8c3147de
-- title:
--   Continuous Lattice: scott Function Subbasis is Open scott
-- statement:
--   The Continuous Lattice construction uses the scott Function Subbasis is Open scott property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L673-L676
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L673-L676

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

theorem Scott1972.ContinuousLattice.scottFunctionSubbasis_isOpen_scott {x : D} {U : Set D'} (hU : @IsOpen D' scottTopologicalSpace U) :
    @IsOpen (ScottC D D') (@scottFunctionTopology D D' scottTopologicalSpace scottTopologicalSpace)
      {f : ScottC D D' | f x ∈ U} := by sorry
