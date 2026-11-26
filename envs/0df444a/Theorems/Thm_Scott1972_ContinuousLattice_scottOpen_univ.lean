-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottOpen_univ
-- name    : Scott1972.ContinuousLattice.scottOpen_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:34.933102+00:00
-- url     : https://prove2.me/theorems/9a0ed947-56b0-452c-99b6-bcbeeade5ba7
-- title:
--   Continuous Lattice: scott Open univ
-- statement:
--   The Continuous Lattice construction uses the scott Open univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L55-L58
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L55-L58

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.scottOpen_univ : ScottOpen (Set.univ : Set D) := by sorry
