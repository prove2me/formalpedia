-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeRetraction_retr_wayBelow_of_wayBelow_incl
-- name    : Scott1972.ContinuousLattice.IsContinuousLatticeRetraction.retr_wayBelow_of_wayBelow_incl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:37:14.453102+00:00
-- url     : https://prove2.me/theorems/2638e181-1f43-41ae-a453-ecca6125b9f0
-- title:
--   Is Continuous Lattice Retraction: retr way Below of way Below incl
-- statement:
--   **Heart of Scott's proof of 2.10.** If `x' ≪ i(d)` in the ambient continuous lattice `D'`,
--   then its image `j(x')` is way below `d` in the retract `D`. The Scott-open witness in `D` is the
--   preimage `i⁻¹V'` of an ambient Scott-open witness `V'` (Scott-open because `i` preserves directed
--   suprema); for `z ∈ i⁻¹V'` we have `x' ⊑ i(z)`, hence `j(x') ⊑ j(i(z)) = z`. No projection
--   hypothesis is needed — `j ∘ i = id` and monotonicity suffice.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L894-L902
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L894-L902

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
open Scott1972.ContinuousLattice.IsContinuousLatticeRetraction

theorem Scott1972.ContinuousLattice.IsContinuousLatticeRetraction.retr_wayBelow_of_wayBelow_incl (R : IsContinuousLatticeRetraction D D')
    {d : D} {x' : D'} (hx' : x' ≪ R.incl d) : R.retr x' ≪ d := by sorry
