-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_specializationLe_scott_iff
-- name    : Scott1972.ContinuousLattice.specializationLe_scott_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:29:21.175912+00:00
-- url     : https://prove2.me/theorems/ec75d00e-ca64-42c9-ac1c-b927c900aed1
-- title:
--   Continuous Lattice: specialization Le scott iff
-- statement:
--   The specialization order of the Scott topology is the original lattice order.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L129-L136
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L129-L136

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

theorem Scott1972.ContinuousLattice.specializationLe_scott_iff {x y : D} :
    @SpecializationLe D scottTopologicalSpace x y ↔ x ≤ y := by sorry
