-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_directedOn_wayBelow
-- name    : Scott1972.ContinuousLattice.directedOn_wayBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:11.403248+00:00
-- url     : https://prove2.me/theorems/01c988bd-c9f7-5089-aeb2-92ed62ea4dc5
-- title:
--   Continuous Lattice: directed On way Below
-- statement:
--   The set `{x | x ≪ y}` of elements way below `y` is directed: it is closed under binary
--   joins by Proposition 2.2(ii) (`WayBelow.sup`). This holds in *any* complete lattice.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L165-L166
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L165-L166

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.directedOn_wayBelow (y : D) : DirectedOn (· ≤ ·) {x | x ≪ y} := by sorry
