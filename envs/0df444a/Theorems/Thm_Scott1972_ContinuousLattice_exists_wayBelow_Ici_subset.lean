-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_exists_wayBelow_Ici_subset
-- name    : Scott1972.ContinuousLattice.exists_wayBelow_Ici_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:45.901177+00:00
-- url     : https://prove2.me/theorems/11c0b627-d105-54d1-b456-67c4a6d01e3f
-- title:
--   Continuous Lattice: exists way Below Ici subset
-- statement:
--   A strengthening of `exists_wayBelow_subset`: the witness `a ≪ z` can be taken with the whole
--   principal up-set `Set.Ici a` (not merely `↟a`) inside `U`. The element `a` produced lies in the
--   open `U`, which is upper, so `↑a ⊆ U`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L211-L216
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L211-L216

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.exists_wayBelow_Ici_subset (hD : IsContinuousLattice D) {U : Set D} (hU : ScottOpen U)
    {z : D} (hz : z ∈ U) : ∃ a, a ≪ z ∧ Set.Ici a ⊆ U := by sorry
