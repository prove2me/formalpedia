-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeProjection_retr_eq_sSup
-- name    : Scott1972.ContinuousLattice.IsContinuousLatticeProjection.retr_eq_sSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:40:09.638313+00:00
-- url     : https://prove2.me/theorems/8e0e3087-59d2-4179-8b39-aee106dc934d
-- title:
--   Is Continuous Lattice Projection: retr eq s Sup
-- statement:
--   **Scott 1972, Proposition 3.10(iv), uniqueness.** The retraction of any projection is forced to
--   be Scott's formula `j(x') = ⊔ { x | i(x) ⊑ x' }`. `≤`: `j(x')` itself satisfies `i(j x') ⊑ x'`
--   (by `i ∘ j ⊑ id`), so it is a member of the set; `≥`: each member `x` (with `i x ⊑ x'`) satisfies
--   `x = j(i x) ⊑ j(x')` by `j ∘ i = id` and monotonicity.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1185-L1191
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1185-L1191

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

theorem Scott1972.ContinuousLattice.IsContinuousLatticeProjection.retr_eq_sSup (P : IsContinuousLatticeProjection D D') (x' : D') :
    (P.retr : D' → D) x' = sSup {x | (P.incl : D → D') x ≤ x'} := by sorry
