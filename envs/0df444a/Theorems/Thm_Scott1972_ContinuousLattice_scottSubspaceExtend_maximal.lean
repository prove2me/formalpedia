-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottSubspaceExtend_maximal
-- name    : Scott1972.ContinuousLattice.scottSubspaceExtend_maximal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:40:40.44366+00:00
-- url     : https://prove2.me/theorems/6b110786-e998-4660-b83a-6a45b7e8e9cf
-- title:
--   Continuous Lattice: scott Subspace Extend maximal
-- statement:
--   **Scott 1972, Proposition 3.8 (subspace variant).** `f̄` (with the Scott topology on `Y`) is
--   the maximal extension along a subspace embedding. The faithful statement (arbitrary topology on
--   `Y`) is `proposition_3_8` in `Constructions.lean`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1374-L1395
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1374-L1395

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

theorem Scott1972.ContinuousLattice.scottSubspaceExtend_maximal (hD : IsContinuousLattice D) (e : X → Y) (_he : IsEmbedding e)
    (f : X → D) (f' : ScottMap Y D) (h_ext : ∀ x, f' (e x) = f x) (y : Y) :
    (f' : Y → D) y ≤ scottSubspaceExtend e f y := by sorry
