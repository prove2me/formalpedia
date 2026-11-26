-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottMapPointwiseTopology_eq_induced_pi
-- name    : Scott1972.ContinuousLattice.scottMapPointwiseTopology_eq_induced_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:36:01.407386+00:00
-- url     : https://prove2.me/theorems/0fc59d55-5cf6-51c6-abc2-7cc4a29773dc
-- title:
--   Continuous Lattice: scott Map Pointwise Topology eq induced pi
-- statement:
--   Scott's manually generated pointwise topology on `ScottMap` is the subspace topology inherited
--   from the literal Pi product of the codomain Scott topology.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L551-L569
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L551-L569

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

theorem Scott1972.ContinuousLattice.scottMapPointwiseTopology_eq_induced_pi :
    scottMapPointwiseTopology D D' = scottMapInducedPiTopology D D' := by sorry
