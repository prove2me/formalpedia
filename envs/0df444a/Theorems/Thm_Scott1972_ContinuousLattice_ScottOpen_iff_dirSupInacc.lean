-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_ScottOpen_iff_dirSupInacc
-- name    : Scott1972.ContinuousLattice.ScottOpen_iff_dirSupInacc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:29:50.599297+00:00
-- url     : https://prove2.me/theorems/861cfa1c-df3d-4202-9477-28d9e0b7f887
-- title:
--   Continuous Lattice: Scott Open iff dir Sup Inacc
-- statement:
--   The Continuous Lattice construction uses the Scott Open iff dir Sup Inacc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L66-L76
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Specialization.lean#L66-L76

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

theorem Scott1972.ContinuousLattice.ScottOpen_iff_dirSupInacc {U : Set D} : ScottOpen U ↔ IsUpperSet U ∧ DirSupInacc U := by sorry
