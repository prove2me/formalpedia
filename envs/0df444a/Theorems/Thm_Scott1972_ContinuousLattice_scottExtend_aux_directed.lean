-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottExtend_aux_directed
-- name    : Scott1972.ContinuousLattice.scottExtend_aux_directed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:49.506206+00:00
-- url     : https://prove2.me/theorems/d0786184-7a7b-5efd-b44b-50aa94c81593
-- title:
--   Continuous Lattice: scott Extend aux directed
-- statement:
--   The defining family of `scottExtend` is directed: open neighbourhoods are closed under
--   intersection, and `⊓ f''(e⁻¹ ·)` is monotone in the neighbourhood (smaller set, larger inf).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L275-L280
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L275-L280

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

theorem Scott1972.ContinuousLattice.scottExtend_aux_directed (e : X → Y) (f : X → E) (y : Y) :
    DirectedOn (· ≤ ·) {d | ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ d = sInf (f '' (e ⁻¹' V))} := by sorry
