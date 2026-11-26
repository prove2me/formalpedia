-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_lemma_3_9_retr_inf
-- name    : Scott1972.ContinuousLattice.lemma_3_9_retr_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:41:11.413493+00:00
-- url     : https://prove2.me/theorems/aad6cd23-e9cb-504d-b8fe-e7cee8983298
-- title:
--   Continuous Lattice: lemma 3 9 retr inf
-- statement:
--   **Scott 1972, Lemma 3.9 (retraction at infimum level).** The global equality
--   `f̄ = j ∘ ḡ` assembles these infimum bounds via Proposition 3.10(i).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1468-L1471
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1468-L1471

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

theorem Scott1972.ContinuousLattice.lemma_3_9_retr_inf {e : X → Y} (P : IsContinuousLatticeProjection D D') {g : X → D'}
    (U : Set Y) :
    P.retr (scottSubspaceExtendInf e g U) ≤ scottSubspaceExtendInf e (fun x => P.retr (g x)) U := by sorry
