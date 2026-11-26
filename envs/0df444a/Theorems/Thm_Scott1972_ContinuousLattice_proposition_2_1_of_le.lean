-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_1_of_le
-- name    : Scott1972.ContinuousLattice.proposition_2_1_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:29:52.681166+00:00
-- url     : https://prove2.me/theorems/d19e8f1d-28b2-4f89-b95c-ad5aff6ecf62
-- title:
--   Continuous Lattice: proposition 2 1 of le
-- statement:
--   **Scott 1972, Proposition 2.1 (backward).** If `y ≤ L` and `L` is  the lub of a monotone
--   net, then the net converges to `y` in the Scott topology.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L104-L116
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L104-L116

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

theorem Scott1972.ContinuousLattice.proposition_2_1_of_le [Nonempty ι] (hx : IsMonotoneNet x) (hL : IsLUB (range x) L)
    (hyL : y ≤ L) : ScottConvergesTo x y := by sorry
