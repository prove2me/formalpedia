-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_isOpen_scott_iff_scottOpen
-- name    : Scott1972.ContinuousLattice.isOpen_scott_iff_scottOpen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:31:17.112859+00:00
-- url     : https://prove2.me/theorems/4ababd2f-a70f-5724-b91d-3c8602573d6e
-- title:
--   Continuous Lattice: is Open scott iff scott Open
-- statement:
--   Scott-open sets in our sense agree with mathlib's Scott topology (alias).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L86-L88
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L86-L88

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

theorem Scott1972.ContinuousLattice.isOpen_scott_iff_scottOpen {U : Set D} :
    @IsOpen D (Topology.scott D univ) U ↔ ScottOpen U := by sorry
