-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_theorem_3_3
-- name    : Scott1972.ContinuousLattice.theorem_3_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:39:00.590631+00:00
-- url     : https://prove2.me/theorems/54aedfde-7b1c-4d48-abc7-950440253e41
-- title:
--   Continuous Lattice: theorem 3 3
-- statement:
--   **Scott 1972, Theorem 3.3 (full statement).** For continuous lattices `D`, `D'`, the function
--   space `[D → D']` is a continuous lattice (`theorem_3_3_isContinuousLattice`) whose Scott topology
--   agrees with the topology of pointwise convergence (`theorem_3_3_topology`).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L666-L669
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L666-L669

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

theorem Scott1972.ContinuousLattice.theorem_3_3 (hD : IsContinuousLattice D) (hD' : IsContinuousLattice D') :
    IsContinuousLattice (ScottMap D D') ∧
      (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) = scottMapPointwiseTopology D D' := by sorry
