-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_pointwiseSubbasic_scottOpen
-- name    : Scott1972.ContinuousLattice.pointwiseSubbasic_scottOpen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:36:04.353055+00:00
-- url     : https://prove2.me/theorems/222af470-b067-5533-9dc6-4d6f8f01bc58
-- title:
--   Continuous Lattice: pointwise Subbasic scott Open
-- statement:
--   Each pointwise-subbasic set `{f | f x ∈ U}` (`U` Scott-open) is Scott-open in the lattice
--   `[D → D']`, because suprema there are pointwise. This is the easy inclusion pointwise ⊆ Scott.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L573-L583
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L573-L583

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

theorem Scott1972.ContinuousLattice.pointwiseSubbasic_scottOpen (x : D) {U : Set D'} (hU : ScottOpen U) :
    ScottOpen {f : ScottMap D D' | (f : D → D') x ∈ U} := by sorry
