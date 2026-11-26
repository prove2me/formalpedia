-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_wayBelow_self_iff_scottOpen_Ici
-- name    : Scott1972.ContinuousLattice.wayBelow_self_iff_scottOpen_Ici
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:44.595446+00:00
-- url     : https://prove2.me/theorems/e809c9be-da9a-5663-a693-045a9db9e1ed
-- title:
--   Continuous Lattice: way Below self iff scott Open Ici
-- statement:
--   **Scott 1972, Proposition 2.2(vi).** `x ≪ x` iff the principal up-set `{z | x ⊑ z}` (i.e.
--   `Set.Ici x`) is Scott-open. This characterizes the *compact* (finite, isolated) elements:
--   `x` is compact exactly when `↑x` is open.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L129-L137
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L129-L137

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.wayBelow_self_iff_scottOpen_Ici {x : D} : x ≪ x ↔ ScottOpen (Set.Ici x) := by sorry
