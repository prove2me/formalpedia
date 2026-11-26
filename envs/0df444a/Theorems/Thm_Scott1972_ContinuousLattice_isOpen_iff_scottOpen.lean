-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_isOpen_iff_scottOpen
-- name    : Scott1972.ContinuousLattice.isOpen_iff_scottOpen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:29:17.482454+00:00
-- url     : https://prove2.me/theorems/7235b91d-1ee5-5c25-bea9-4ca772eaa9c8
-- title:
--   Continuous Lattice: is Open iff scott Open
-- statement:
--   The Continuous Lattice construction uses the is Open iff scott Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L78-L83
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L78-L83

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

theorem Scott1972.ContinuousLattice.isOpen_iff_scottOpen {U : Set D} : @IsOpen D scottTopologicalSpace U ↔ ScottOpen U := by sorry
