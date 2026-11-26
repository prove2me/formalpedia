-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_sup
-- name    : Scott1972.ContinuousLattice.WayBelow.sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:06.958129+00:00
-- url     : https://prove2.me/theorems/de117c69-6d4a-557a-a8b6-133545a869cd
-- title:
--   Way Below: sup
-- statement:
--   **Scott 1972, Proposition 2.2(ii).** `x ≪ z` and `y ≪ z` imply `x ⊔ y ≪ z`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L111-L115
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L111-L115

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.WayBelow.sup {x y z : D} (hx : x ≪ z) (hy : y ≪ z) : x ⊔ y ≪ z := by sorry
