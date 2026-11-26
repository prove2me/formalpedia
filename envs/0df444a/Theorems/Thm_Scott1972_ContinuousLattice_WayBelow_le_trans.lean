-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le_trans
-- name    : Scott1972.ContinuousLattice.WayBelow.le_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:06.7905+00:00
-- url     : https://prove2.me/theorems/d74f40b5-0c9a-4a59-b640-6561ad71b062
-- title:
--   Way Below: le trans
-- statement:
--   **Scott 1972, Proposition 2.2(iv).** `x ≤ y` and `y ≪ z` imply `x ≪ z` (monotone on the
--   left).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L104-L108
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L104-L108

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.WayBelow.le_trans {x y z : D} (hxy : x ≤ y) (h : y ≪ z) : x ≪ z := by sorry
