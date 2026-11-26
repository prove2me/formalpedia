-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_stepMap_pointwise_sSup
-- name    : Scott1972.ContinuousLattice.stepMap_pointwise_sSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:35:06.024311+00:00
-- url     : https://prove2.me/theorems/2dbf1c9d-8f2c-4135-aa11-c6e026257f54
-- title:
--   Continuous Lattice: step Map pointwise s Sup
-- statement:
--   **Pointwise reconstruction.** For a Scott map `f`, the supremum of the values of the step
--   functions below `f` recovers `f x`: `f x = ⊔ {e' | ∃ e ≪ x, e' ≪ f e}`. Uses continuity of `D`
--   (`x = ⊔{e | e ≪ x}`), Scott-continuity of `f`, and continuity of `D'`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L471-L491
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L471-L491

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

theorem Scott1972.ContinuousLattice.stepMap_pointwise_sSup (hD : IsContinuousLattice D) (hD' : IsContinuousLattice D')
    (f : ScottMap D D') (x : D) :
    sSup {e' : D' | ∃ e, e ≪ x ∧ e' ≪ (f : D → D') e} = (f : D → D') x := by sorry
