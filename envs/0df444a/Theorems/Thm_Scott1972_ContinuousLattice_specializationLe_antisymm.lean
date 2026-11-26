-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_specializationLe_antisymm
-- name    : Scott1972.ContinuousLattice.specializationLe_antisymm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:31:13.639016+00:00
-- url     : https://prove2.me/theorems/852906cd-b8cb-4075-810f-0ab5c457cb1e
-- title:
--   Continuous Lattice: specialization Le antisymm
-- statement:
--   The Continuous Lattice construction uses the specialization Le antisymm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L42-L46
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L42-L46

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

theorem Scott1972.ContinuousLattice.specializationLe_antisymm [T0Space X] {x y : X}
    (hxy : SpecializationLe x y) (hyx : SpecializationLe y x) : x = y := by sorry
