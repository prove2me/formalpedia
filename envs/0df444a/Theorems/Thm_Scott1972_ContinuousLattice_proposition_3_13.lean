-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_3_13
-- name    : Scott1972.ContinuousLattice.proposition_3_13
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:41:21.511634+00:00
-- url     : https://prove2.me/theorems/07abd14b-9713-5f7c-8eab-e05cb1ecf14a
-- title:
--   Continuous Lattice: proposition 3 13
-- statement:
--   **Scott 1972, Proposition 3.13.** Every continuous lattice `D` is a projection of its function
--   space `[D → D]`, via `con`/`min` (`Proposition313.projection`).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1663-L1665
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1663-L1665

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

theorem Scott1972.ContinuousLattice.proposition_3_13 (_hD : IsContinuousLattice D) :
    Nonempty (IsContinuousLatticeProjection D (ScottMap D D)) := by sorry
