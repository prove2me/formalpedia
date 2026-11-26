-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_trans_le
-- name    : Scott1972.ContinuousLattice.WayBelow.trans_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:10.315635+00:00
-- url     : https://prove2.me/theorems/f4a67b62-0f98-4fcf-82e7-80b778ce610b
-- title:
--   Way Below: trans le
-- statement:
--   **Scott 1972, Proposition 2.2(iii).** `x ≪ y` and `y ≤ z` imply `x ≪ z` (monotone on the
--   right).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L98-L100
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L98-L100

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.WayBelow.trans_le {x y z : D} (h : x ≪ y) (hyz : y ≤ z) : x ≪ z := by sorry
