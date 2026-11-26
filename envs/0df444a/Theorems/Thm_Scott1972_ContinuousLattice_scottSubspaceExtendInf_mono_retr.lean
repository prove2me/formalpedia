-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottSubspaceExtendInf_mono_retr
-- name    : Scott1972.ContinuousLattice.scottSubspaceExtendInf_mono_retr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:37:46.800953+00:00
-- url     : https://prove2.me/theorems/c54d033e-7532-573c-8b4b-e0d19dd1b7bd
-- title:
--   Continuous Lattice: scott Subspace Extend Inf mono retr
-- statement:
--   The Continuous Lattice construction uses the scott Subspace Extend Inf mono retr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1429-L1436
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1429-L1436

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

theorem Scott1972.ContinuousLattice.scottSubspaceExtendInf_mono_retr {e : X → Y} {g : X → D'}
    (P : IsContinuousLatticeProjection D D') (U : Set Y) :
    P.retr (scottSubspaceExtendInf e g U) ≤ scottSubspaceExtendInf e (fun x => P.retr (g x)) U := by sorry
