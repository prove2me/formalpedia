-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_corollary_3_4
-- name    : Scott1972.ContinuousLattice.corollary_3_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:39:10.629819+00:00
-- url     : https://prove2.me/theorems/e030f4df-d3ce-52b6-ad78-afc11061d24a
-- title:
--   Continuous Lattice: corollary 3 4
-- statement:
--   **Scott 1972, Corollary 3.4 (fixed `x`).** Evaluation at fixed `x` is continuous on `[D → D']`
--   (with Scott topologies on `D` and `D'`); this is one half of the separate-continuity input to
--   joint continuity.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L687-L691
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L687-L691

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

theorem Scott1972.ContinuousLattice.corollary_3_4 (x : D) :
    @Continuous (ScottC D D') D'
      (@scottFunctionTopology D D' scottTopologicalSpace scottTopologicalSpace)
      scottTopologicalSpace (fun f : ScottC D D' => f x) := by sorry
