-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLatticeProjection_proposition_3_10_forward
-- name    : Scott1972.ContinuousLattice.IsContinuousLatticeProjection.proposition_3_10_forward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:40:13.235826+00:00
-- url     : https://prove2.me/theorems/78044197-f59e-403b-80f2-d30220d9317e
-- title:
--   Is Continuous Lattice Projection: proposition 3 10 forward
-- statement:
--   **Scott 1972, Proposition 3.10(i)–(iii), bundled.** The inclusion `i` of a projection preserves
--   arbitrary suprema, is injective, and preserves the way-below relation.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1173-L1179
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1173-L1179

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

theorem Scott1972.ContinuousLattice.IsContinuousLatticeProjection.proposition_3_10_forward (P : IsContinuousLatticeProjection D D')
    (hD' : IsContinuousLattice D') :
    (∀ S : Set D, (P.incl : D → D') (sSup S) = sSup (Set.image (P.incl : D → D') S))
      ∧ Function.Injective (P.incl : D → D')
      ∧ (∀ x y : D, x ≪ y → (P.incl : D → D') x ≪ (P.incl : D → D') y) := by sorry
