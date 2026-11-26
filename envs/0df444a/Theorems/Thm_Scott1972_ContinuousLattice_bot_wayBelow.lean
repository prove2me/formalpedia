-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_bot_wayBelow
-- name    : Scott1972.ContinuousLattice.bot_wayBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:09.643787+00:00
-- url     : https://prove2.me/theorems/a5d45e98-6598-4467-88f9-97ed32e1f042
-- title:
--   Continuous Lattice: bot way Below
-- statement:
--   **Scott 1972, Proposition 2.2(i).** `⊥ ≪ x` for every `x`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L93-L94
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L93-L94

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.bot_wayBelow (x : D) : (⊥ : D) ≪ x := by sorry
