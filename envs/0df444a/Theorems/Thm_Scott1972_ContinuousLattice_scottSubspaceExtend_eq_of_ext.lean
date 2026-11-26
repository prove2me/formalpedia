-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottSubspaceExtend_eq_of_ext
-- name    : Scott1972.ContinuousLattice.scottSubspaceExtend_eq_of_ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:40:56.846005+00:00
-- url     : https://prove2.me/theorems/48020478-7d6f-54a1-a0f7-d2e410be2ed6
-- title:
--   Continuous Lattice: scott Subspace Extend eq of ext
-- statement:
--   The Continuous Lattice construction uses the scott Subspace Extend eq of ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1422-L1427
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1422-L1427

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

theorem Scott1972.ContinuousLattice.scottSubspaceExtend_eq_of_ext {e : X → Y} {f g' : X → D} (h : ∀ x, f x = g' x) (y : Y) :
    scottSubspaceExtend e f y = scottSubspaceExtend e g' y := by sorry
