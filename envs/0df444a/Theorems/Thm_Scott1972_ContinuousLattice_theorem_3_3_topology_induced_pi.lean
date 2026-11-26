-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_theorem_3_3_topology_induced_pi
-- name    : Scott1972.ContinuousLattice.theorem_3_3_topology_induced_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:36:15.03285+00:00
-- url     : https://prove2.me/theorems/e1aa9fa7-ffff-5c3d-9612-dbe2c5f9fa93
-- title:
--   Continuous Lattice: theorem 3 3 topology induced pi
-- statement:
--   The literal product/subspace form of Theorem 3.3: the Scott lattice topology on `[D → D']`
--   is induced from Mathlib's Pi topology on the underlying functions.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L657-L661
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L657-L661

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

theorem Scott1972.ContinuousLattice.theorem_3_3_topology_induced_pi (hD : IsContinuousLattice D)
    (hD' : IsContinuousLattice D') :
    (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) =
      scottMapInducedPiTopology D D' := by sorry
