-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottSubspaceExtendInf_mono_incl
-- name    : Scott1972.ContinuousLattice.scottSubspaceExtendInf_mono_incl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:37:49.109025+00:00
-- url     : https://prove2.me/theorems/ab4859cc-57a9-52b3-abd9-a14b4090649f
-- title:
--   Continuous Lattice: scott Subspace Extend Inf mono incl
-- statement:
--   The Continuous Lattice construction uses the scott Subspace Extend Inf mono incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1438-L1448
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1438-L1448

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

theorem Scott1972.ContinuousLattice.scottSubspaceExtendInf_mono_incl {e : X → Y} {f : X → D} {g : X → D'}
    (P : IsContinuousLatticeProjection D D') (hfg : ∀ x, f x = P.retr (g x)) (U : Set Y) :
    scottSubspaceExtendInf e (fun x => P.incl (f x)) U ≤ scottSubspaceExtendInf e g U := by sorry
