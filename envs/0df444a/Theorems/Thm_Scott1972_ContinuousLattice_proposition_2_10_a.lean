-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_10_a
-- name    : Scott1972.ContinuousLattice.proposition_2_10_a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:35:34.516597+00:00
-- url     : https://prove2.me/theorems/38e48d64-68f2-4c7c-a789-d7a397b40fb0
-- title:
--   Continuous Lattice: proposition 2 10 a
-- statement:
--   **Scott 1972, Proposition 2.10(a).** A (Scott-continuous) retract of a continuous lattice is a
--   continuous lattice. For `d ∈ D` we have, in the ambient `D'`, `i(d) = ⊔{x' | x' ≪ i(d)}`; applying
--   the retraction `j` (which preserves this directed supremum) gives `d = ⊔{j(x') | x' ≪ i(d)}` in
--   `D`, and each `j(x') ≪ d` by `retr_wayBelow_of_wayBelow_incl`. Hence any upper bound of
--   `{x | x ≪ d}` dominates `d`, so `d = ⊔{x | x ≪ d}`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L933-L938
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L933-L938

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

theorem Scott1972.ContinuousLattice.proposition_2_10_a (R : IsContinuousLatticeRetraction D D')
    (hD' : IsContinuousLattice D') : IsContinuousLattice D := by sorry
