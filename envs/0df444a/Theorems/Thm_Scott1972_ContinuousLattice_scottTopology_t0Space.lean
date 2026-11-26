-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottTopology_t0Space
-- name    : Scott1972.ContinuousLattice.scottTopology_t0Space
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:29:56.301228+00:00
-- url     : https://prove2.me/theorems/95134cbc-9135-466d-8203-0c13942e46d9
-- title:
--   Continuous Lattice: scott Topology t0 Space
-- statement:
--   The Scott topology of a partial order is `T₀`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L139-L149
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L139-L149

import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Order.DirSupClosed
import Definitions.Def_Scott1972_ContinuousLattice_Specialization
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
universe u
variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]
variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
variable {x : ι → D} {L y : D}

theorem Scott1972.ContinuousLattice.scottTopology_t0Space : @T0Space D scottTopologicalSpace := by sorry
