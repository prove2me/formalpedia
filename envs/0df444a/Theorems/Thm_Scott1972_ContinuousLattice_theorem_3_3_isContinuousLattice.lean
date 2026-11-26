-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_theorem_3_3_isContinuousLattice
-- name    : Scott1972.ContinuousLattice.theorem_3_3_isContinuousLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:34:55.708679+00:00
-- url     : https://prove2.me/theorems/d6ea16f3-8d14-5861-94f7-64e9443e1572
-- title:
--   Continuous Lattice: theorem 3 3 is Continuous Lattice
-- statement:
--   **Scott 1972, Theorem 3.3 (order content).** If `D` and `D'` are continuous lattices, then so
--   is `[D → D']` under the pointwise order. Every `f` is the supremum of the step functions way below
--   it: `f = ⊔ {ē[e,e'] | e' ≪ f e}`, and each such step function is way below `f`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L496-L507
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L496-L507

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

theorem Scott1972.ContinuousLattice.theorem_3_3_isContinuousLattice (hD : IsContinuousLattice D)
    (hD' : IsContinuousLattice D') : IsContinuousLattice (ScottMap D D') := by sorry
