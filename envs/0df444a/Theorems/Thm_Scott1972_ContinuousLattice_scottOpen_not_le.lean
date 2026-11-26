-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottOpen_not_le
-- name    : Scott1972.ContinuousLattice.scottOpen_not_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:29:25.426014+00:00
-- url     : https://prove2.me/theorems/837382ab-ff3e-5705-905f-ba9735c47c2c
-- title:
--   Continuous Lattice: scott Open not le
-- statement:
--   The complement of a principal lower set `Iic L` is Scott-open: it is an upper set, and it
--   is inaccessible by directed suprema because if every member of a directed `S` lies below `L`
--   then so does `⊔S`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L121-L126
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L121-L126

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

theorem Scott1972.ContinuousLattice.scottOpen_not_le (L : D) : ScottOpen {z : D | ¬ z ≤ L} := by sorry
