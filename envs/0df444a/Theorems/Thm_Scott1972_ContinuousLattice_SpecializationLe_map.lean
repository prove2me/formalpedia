-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_SpecializationLe_map
-- name    : Scott1972.ContinuousLattice.SpecializationLe.map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:29:43.615659+00:00
-- url     : https://prove2.me/theorems/47eba7b3-1f2c-5edb-aed9-7b57115aceee
-- title:
--   Specialization Le: map
-- statement:
--   Continuous maps preserve Scott's specialization order.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L54-L58
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L54-L58

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

theorem Scott1972.ContinuousLattice.SpecializationLe.map {Y : Type*} [TopologicalSpace Y] {x y : X}
    (hxy : SpecializationLe x y) {f : X → Y} (hf : Continuous f) :
    SpecializationLe (f x) (f y) := by sorry
