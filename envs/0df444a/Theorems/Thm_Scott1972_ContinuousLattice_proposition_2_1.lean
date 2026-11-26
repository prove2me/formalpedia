-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_1
-- name    : Scott1972.ContinuousLattice.proposition_2_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:31:21.851798+00:00
-- url     : https://prove2.me/theorems/702854f2-1b24-5509-b999-3a2c4855cfd8
-- title:
--   Continuous Lattice: proposition 2 1
-- statement:
--   **Scott 1972, Proposition 2.1.** A monotone net with least upper bound `L` converges to
--   `y` in the Scott topology iff `y ⊑ L = ⊔ {xᵢ}`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L162-L164
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L162-L164

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

theorem Scott1972.ContinuousLattice.proposition_2_1 [Nonempty ι] (hx : IsMonotoneNet x) (hL : IsLUB (range x) L) :
    ScottConvergesTo x y ↔ y ≤ L := by sorry
