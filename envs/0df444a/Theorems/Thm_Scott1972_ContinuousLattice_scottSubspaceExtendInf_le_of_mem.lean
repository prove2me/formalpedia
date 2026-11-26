-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottSubspaceExtendInf_le_of_mem
-- name    : Scott1972.ContinuousLattice.scottSubspaceExtendInf_le_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:37:35.245719+00:00
-- url     : https://prove2.me/theorems/f813df49-f740-438d-94a4-e5d9132361be
-- title:
--   Continuous Lattice: scott Subspace Extend Inf le of mem
-- statement:
--   The Continuous Lattice construction uses the scott Subspace Extend Inf le of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1315-L1317
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1315-L1317

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
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y]
omit [TopologicalSpace Y]

theorem Scott1972.ContinuousLattice.scottSubspaceExtendInf_le_of_mem {f' : ScottMap Y D} {U : Set Y} {y : Y}
    (hyU : y ∈ U) : sInf (Set.image (f' : Y → D) U) ≤ f' y := by sorry
