-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_10_b
-- name    : Scott1972.ContinuousLattice.proposition_2_10_b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:35:31.902795+00:00
-- url     : https://prove2.me/theorems/e9146b71-5321-549e-a26f-37bc01536b38
-- title:
--   Continuous Lattice: proposition 2 10 b
-- statement:
--   **Scott 1972, Proposition 2.10(b) (March 1972 / Milner correction).** The Scott topology of the
--   retract `D` coincides with the subspace topology induced from the ambient `D'` along `i`.
--
--   * `scott ≤ induced`: each induced-open `i⁻¹V'` is Scott-open in `D` because `i` is a Scott map.
--   * `induced ≤ scott`: the sets `i⁻¹(↟x') = {z | x' ≪ i(z)}` (`x' ∈ D'`) are a basis of `D`'s Scott
--     topology — given a Scott-open `U ∋ d`, the directed family `{j(x') | x' ≪ i(d)}` (sup `d`) meets
--     `U` at some `j(x')`, and `i⁻¹(↟x') ⊆ U` since `x' ≪ i(z) ⟹ j(x') ⊑ z` with `U` upper. Each such
--     basic set is induced-open by construction, so every Scott-open of `D` is induced-open.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L948-L973
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L948-L973

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

theorem Scott1972.ContinuousLattice.proposition_2_10_b (R : IsContinuousLatticeRetraction D D')
    (hD' : IsContinuousLattice D') :
    (scottTopologicalSpace : TopologicalSpace D) =
      TopologicalSpace.induced (R.incl : D → D') scottTopologicalSpace := by sorry
