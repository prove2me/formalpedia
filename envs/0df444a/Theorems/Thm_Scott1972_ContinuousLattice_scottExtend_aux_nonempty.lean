-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottExtend_aux_nonempty
-- name    : Scott1972.ContinuousLattice.scottExtend_aux_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:46.995402+00:00
-- url     : https://prove2.me/theorems/d66bb0bd-d022-55f5-b5de-6616576b0b58
-- title:
--   Continuous Lattice: scott Extend aux nonempty
-- statement:
--   The Continuous Lattice construction uses the scott Extend aux nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L269-L271
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L269-L271

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]

theorem Scott1972.ContinuousLattice.scottExtend_aux_nonempty (e : X → Y) (f : X → E) (y : Y) :
    {d | ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ d = sInf (f '' (e ⁻¹' V))}.Nonempty := by sorry
