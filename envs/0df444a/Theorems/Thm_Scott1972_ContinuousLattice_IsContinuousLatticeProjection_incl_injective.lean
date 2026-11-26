-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeProjection_incl_injective
-- name    : Scott1972.ContinuousLattice.IsContinuousLatticeProjection.incl_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:37:17.790774+00:00
-- url     : https://prove2.me/theorems/def7ef48-dce9-5b40-bfb4-b4c511d4757b
-- title:
--   Is Continuous Lattice Projection: incl injective
-- statement:
--   **Scott 1972, Proposition 3.10(ii).** The inclusion map of a projection is injective.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1047-L1048
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1047-L1048

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
open Finset
open Scott1972.ContinuousLattice.IsContinuousLatticeProjection

theorem Scott1972.ContinuousLattice.IsContinuousLatticeProjection.incl_injective (P : IsContinuousLatticeProjection D D') {x y : D} (h : P.incl x = P.incl y) : x = y := by sorry
