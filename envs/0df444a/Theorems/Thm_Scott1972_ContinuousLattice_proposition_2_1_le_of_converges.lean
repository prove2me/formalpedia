-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_1_le_of_converges
-- name    : Scott1972.ContinuousLattice.proposition_2_1_le_of_converges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:29:56.386641+00:00
-- url     : https://prove2.me/theorems/8a57c6b0-d0f0-517c-a1c3-a29a8345adf5
-- title:
--   Continuous Lattice: proposition 2 1 le of converges
-- statement:
--   **Scott 1972, Proposition 2.1 (forward).** If a monotone net converges to `y` in the Scott
--   topology and `L` is its least upper bound, then `y ≤ L`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L154-L158
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L154-L158

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
omit [IsDirected ι (· ≤ ·)]

theorem Scott1972.ContinuousLattice.proposition_2_1_le_of_converges (hL : IsLUB (range x) L)
    (hconv : ScottConvergesTo x y) : y ≤ L := by sorry
