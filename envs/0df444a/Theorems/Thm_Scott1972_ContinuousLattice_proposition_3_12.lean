-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_3_12
-- name    : Scott1972.ContinuousLattice.proposition_3_12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:41:14.294958+00:00
-- url     : https://prove2.me/theorems/0f488514-53f7-564d-be20-cdd64042c180
-- title:
--   Continuous Lattice: proposition 3 12
-- statement:
--   **Scott 1972, Proposition 3.12.** For a (complete, in particular continuous) lattice `D`, the
--   projections `J_D` form a complete lattice as a `⊔`-closed subspace of `[D → D]`: the `⊔`-closure is
--   `isProjection_sSup`, and the complete-lattice structure is `Projections.instCompleteLattice`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1613-L1616
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1613-L1616

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

theorem Scott1972.ContinuousLattice.proposition_3_12 :
    (∀ T : Set (ScottMap D D), (∀ j ∈ T, IsProjection j) → IsProjection (sSup T))
      ∧ Nonempty (CompleteLattice (Projections D)) := by sorry
