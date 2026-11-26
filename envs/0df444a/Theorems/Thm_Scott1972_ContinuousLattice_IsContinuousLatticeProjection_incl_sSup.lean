-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeProjection_incl_sSup
-- name    : Scott1972.ContinuousLattice.IsContinuousLatticeProjection.incl_sSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:37:34.130975+00:00
-- url     : https://prove2.me/theorems/bc52ed8f-8955-4ff4-befb-1f1a199610a9
-- title:
--   Is Continuous Lattice Projection: incl s Sup
-- statement:
--   **Scott 1972, Proposition 3.10(i).** Projections preserve arbitrary suprema.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1117-L1142
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1117-L1142

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

theorem Scott1972.ContinuousLattice.IsContinuousLatticeProjection.incl_sSup (P : IsContinuousLatticeProjection D D') (S : Set D) :
    P.incl (sSup S) = sSup (Set.image (P.incl : D → D') S) := by sorry
