-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le
-- name    : Scott1972.ContinuousLattice.WayBelow.le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:05.520655+00:00
-- url     : https://prove2.me/theorems/57e713c3-c6e9-4fb7-98ba-48b655b56734
-- title:
--   Way Below: le
-- statement:
--   **Scott 1972, Proposition 2.2(v).** `x ≪ y` implies `x ≤ y`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L88-L90
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L88-L90

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.WayBelow.le {x y : D} (h : x ≪ y) : x ≤ y := by sorry
