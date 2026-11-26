-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_corollary_3_4_jointly_continuous
-- name    : Scott1972.ContinuousLattice.corollary_3_4_jointly_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:39:14.273744+00:00
-- url     : https://prove2.me/theorems/c4647778-de54-4c73-9ebd-a658b670d480
-- title:
--   Continuous Lattice: corollary 3 4 jointly continuous
-- statement:
--   **Scott 1972, Corollary 3.4.** The evaluation map `eval : [D → D'] × D → D'`, `(f, x) ↦ f x`,
--   is (jointly) Scott-continuous. Via Theorem 3.3(b) and Proposition 2.9(b) the Scott topology of the
--   product lattice is the product of the pointwise topology on `[D → D']` and the Scott topology on
--   `D`, so this is exactly joint continuity for Scott's product topology.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L712-L715
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L712-L715

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

theorem Scott1972.ContinuousLattice.corollary_3_4_jointly_continuous :
    @Continuous (ScottMap D D' × D) D' scottTopologicalSpace scottTopologicalSpace
      (fun p : ScottMap D D' × D => (p.1 : D → D') p.2) := by sorry
