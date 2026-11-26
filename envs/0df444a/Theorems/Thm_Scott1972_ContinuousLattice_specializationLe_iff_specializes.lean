-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_specializationLe_iff_specializes
-- name    : Scott1972.ContinuousLattice.specializationLe_iff_specializes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:29:24.907724+00:00
-- url     : https://prove2.me/theorems/b108c959-3579-56c5-bdb0-124ed3fc443a
-- title:
--   Continuous Lattice: specialization Le iff specializes
-- statement:
--   Scott's specialization order is the reverse of Mathlib's `Specializes` convention.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L49-L51
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L49-L51

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

theorem Scott1972.ContinuousLattice.specializationLe_iff_specializes {x y : X} :
    SpecializationLe x y ↔ y ⤳ x := by sorry
