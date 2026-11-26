-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottOpen_inter
-- name    : Scott1972.ContinuousLattice.scottOpen_inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:33.946443+00:00
-- url     : https://prove2.me/theorems/2f8803d8-0264-4229-8fcb-5970baa78989
-- title:
--   Continuous Lattice: scott Open inter
-- statement:
--   The Continuous Lattice construction uses the scott Open inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L60-L66
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L60-L66

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.scottOpen_inter {U V : Set D} (hU : ScottOpen U) (hV : ScottOpen V) :
    ScottOpen (U ∩ V) := by sorry
