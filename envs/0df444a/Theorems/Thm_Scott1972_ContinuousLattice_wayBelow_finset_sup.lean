-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_wayBelow_finset_sup
-- name    : Scott1972.ContinuousLattice.wayBelow_finset_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:36:08.766933+00:00
-- url     : https://prove2.me/theorems/2440d3fa-4ee0-46cc-9064-a12a620fa824
-- title:
--   Continuous Lattice: way Below finset sup
-- statement:
--   A finite sup of elements way below `g` is way below `g`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L519-L521
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L519-L521

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_sup

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem Scott1972.ContinuousLattice.wayBelow_finset_sup {ι L : Type*} [CompleteLattice L] {s : Finset ι} {f : ι → L} {g : L}
    (h : ∀ i ∈ s, f i ≪ g) : s.sup f ≪ g := by sorry
