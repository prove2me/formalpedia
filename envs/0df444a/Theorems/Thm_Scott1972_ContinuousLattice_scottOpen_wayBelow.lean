-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottOpen_wayBelow
-- name    : Scott1972.ContinuousLattice.scottOpen_wayBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:10.708635+00:00
-- url     : https://prove2.me/theorems/b2c900ab-9aa1-4b00-a6ca-05a465736cac
-- title:
--   Continuous Lattice: scott Open way Below
-- statement:
--   Auxiliary: the up-set `{z | x ≪ z}` is itself Scott-open. (This is *not* Scott's
--   Proposition 2.2(vi) — see `wayBelow_self_iff_scottOpen_Ici` for that — but it is a standard
--   and useful fact, the openness of the sets `↟x`.)
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L120-L124
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L120-L124

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.scottOpen_wayBelow (x : D) : ScottOpen {z | x ≪ z} := by sorry
