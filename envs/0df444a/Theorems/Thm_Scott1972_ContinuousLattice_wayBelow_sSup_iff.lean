-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_wayBelow_sSup_iff
-- name    : Scott1972.ContinuousLattice.wayBelow_sSup_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:08.730267+00:00
-- url     : https://prove2.me/theorems/ba6c2263-c59f-45fd-b441-c3bb8ae2ae74
-- title:
--   Continuous Lattice: way Below s Sup iff
-- statement:
--   **Scott 1972, Proposition 2.2(vii).** For a non-empty directed set `S`, `x ≪ ⊔S` iff
--   `x ≪ y` for some `y ∈ S`. The forward direction is exactly inaccessibility of a Scott-open
--   set; the backward direction is monotonicity on the right.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L142-L149
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L142-L149

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.wayBelow_sSup_iff {x : D} {S : Set D} (hS : S.Nonempty)
    (hSdir : DirectedOn (· ≤ ·) S) : x ≪ sSup S ↔ ∃ y ∈ S, x ≪ y := by sorry
