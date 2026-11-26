-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottOpen_sUnion
-- name    : Scott1972.ContinuousLattice.scottOpen_sUnion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:29:06.362609+00:00
-- url     : https://prove2.me/theorems/3126a75d-1dfd-5939-bf55-d9c49a47e3cb
-- title:
--   Continuous Lattice: scott Open s Union
-- statement:
--   The Continuous Lattice construction uses the scott Open s Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L68-L73
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L68-L73

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.scottOpen_sUnion {C : Set (Set D)} (hC : ∀ U ∈ C, ScottOpen U) :
    ScottOpen (⋃₀ C) := by sorry
