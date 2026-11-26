-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_corollary_3_4_preservesDirectedSup
-- name    : Scott1972.ContinuousLattice.corollary_3_4_preservesDirectedSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:36:31.583655+00:00
-- url     : https://prove2.me/theorems/fdb0cdab-c22b-4562-b94d-a0a35dde9859
-- title:
--   Continuous Lattice: corollary 3 4 preserves Directed Sup
-- statement:
--   **Scott 1972, Corollary 3.4 (joint continuity, core).** Evaluation `[D → D'] × D → D'`,
--   `(f, x) ↦ f x`, preserves directed suprema. By Proposition 2.6 it suffices to check separate
--   Scott-continuity: in `x` (with `f` fixed) it is `f`'s own continuity, and in `f` (with `x` fixed)
--   it is the pointwise formula for suprema in `[D → D']` (`ScottMap.sSup_apply`).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L697-L706
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean#L697-L706

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

theorem Scott1972.ContinuousLattice.corollary_3_4_preservesDirectedSup :
    PreservesDirectedSup (fun p : ScottMap D D' × D => (p.1 : D → D') p.2) := by sorry
