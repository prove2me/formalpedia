-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_theorem_3_3_topology
-- name    : Scott1972.ContinuousLattice.theorem_3_3_topology
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:35:19.922323+00:00
-- url     : https://prove2.me/theorems/ec66a0c7-1ae5-5fa9-8130-3778cdc5ff43
-- title:
--   Continuous Lattice: theorem 3 3 topology
-- statement:
--   **Scott 1972, Theorem 3.3(b).** The Scott (lattice) topology on `[D → D']` agrees with the
--   topology of pointwise convergence.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L632-L653
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L632-L653

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

theorem Scott1972.ContinuousLattice.theorem_3_3_topology (hD : IsContinuousLattice D) (hD' : IsContinuousLattice D') :
    (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) = scottMapPointwiseTopology D D' := by sorry
