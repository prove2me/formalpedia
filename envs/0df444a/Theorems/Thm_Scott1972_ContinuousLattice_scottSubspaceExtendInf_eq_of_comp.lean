-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottSubspaceExtendInf_eq_of_comp
-- name    : Scott1972.ContinuousLattice.scottSubspaceExtendInf_eq_of_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:37:38.974478+00:00
-- url     : https://prove2.me/theorems/b526a940-41ba-5162-91f9-fe8db212f60f
-- title:
--   Continuous Lattice: scott Subspace Extend Inf eq of comp
-- statement:
--   The Continuous Lattice construction uses the scott Subspace Extend Inf eq of comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1355-L1369
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L1355-L1369

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

theorem Scott1972.ContinuousLattice.scottSubspaceExtendInf_eq_of_comp {e : X → Y} {f : X → D} {U : Set Y}
    (f' : ScottMap Y D) (h : ∀ x, f' (e x) = f x) :
    scottSubspaceExtendInf e f U = sInf (Set.image (f' : Y → D) (Set.image e Set.univ ∩ U)) := by sorry
