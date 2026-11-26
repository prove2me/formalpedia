-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_ScottOpen_isUpperSet
-- name    : Scott1972.ContinuousLattice.ScottOpen.isUpperSet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:29:01.75989+00:00
-- url     : https://prove2.me/theorems/4de04c3c-606d-51ce-aa28-9a3ad65e4476
-- title:
--   Scott Open: is Upper Set
-- statement:
--   The Scott Open construction uses the is Upper Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L53-L53
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L53-L53

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.ScottOpen.isUpperSet {U : Set D} (h : ScottOpen U) : IsUpperSet U := by sorry
