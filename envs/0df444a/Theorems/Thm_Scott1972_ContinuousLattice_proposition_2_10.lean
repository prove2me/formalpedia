-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_10
-- name    : Scott1972.ContinuousLattice.proposition_2_10
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:39:32.692915+00:00
-- url     : https://prove2.me/theorems/a22df4e1-624a-469e-9710-1eb99bd5df48
-- title:
--   Continuous Lattice: proposition 2 10
-- statement:
--   **Scott 1972, Proposition 2.10 (full statement).** A retract of a continuous lattice is a
--   continuous lattice (`proposition_2_10_a`) whose Scott topology agrees with the subspace topology
--   (`proposition_2_10_b`).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L978-L983
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L978-L983

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

theorem Scott1972.ContinuousLattice.proposition_2_10 (R : IsContinuousLatticeRetraction D D')
    (hD' : IsContinuousLattice D') :
    IsContinuousLattice D ∧
      (scottTopologicalSpace : TopologicalSpace D) =
        TopologicalSpace.induced (R.incl : D → D') scottTopologicalSpace := by sorry
