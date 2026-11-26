-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_lemma_3_9_incl_inf
-- name    : Scott1972.ContinuousLattice.lemma_3_9_incl_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:41:09.883689+00:00
-- url     : https://prove2.me/theorems/ef10d44d-9f56-491b-a01a-079775e8b54c
-- title:
--   Continuous Lattice: lemma 3 9 incl inf
-- statement:
--   **Scott 1972, Lemma 3.9 (inclusion at infimum level).** Used in the inverse-limit
--   argument (Theorem 4.4).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1460-L1464
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1460-L1464

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

theorem Scott1972.ContinuousLattice.lemma_3_9_incl_inf {e : X → Y} (P : IsContinuousLatticeProjection D D')
    {f : X → D} {g : X → D'} (hfg : ∀ x, f x = P.retr (g x)) (U : Set Y) :
    P.incl (scottSubspaceExtendInf e f U) ≤ scottSubspaceExtendInf e g U := by sorry
