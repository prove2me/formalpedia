-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_exists_wayBelow_subset
-- name    : Scott1972.ContinuousLattice.exists_wayBelow_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:30.46241+00:00
-- url     : https://prove2.me/theorems/0f0e291c-ba6e-5b91-9200-5b9ad7d0bc9a
-- title:
--   Continuous Lattice: exists way Below subset
-- statement:
--   In a continuous lattice the sets `↟a = {z | a ≪ z}` form a basis of the Scott topology:
--   every Scott-open `U` containing `z` contains some basic neighbourhood `↟a` of `z`. Indeed
--   `z = ⊔{a | a ≪ z}` is a directed supremum lying in the open set `U`, so some `a ≪ z` already
--   lies in `U`, and then `↟a ⊆ ↑a ⊆ U`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L201-L206
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L201-L206

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.exists_wayBelow_subset (hD : IsContinuousLattice D) {U : Set D} (hU : ScottOpen U)
    {z : D} (hz : z ∈ U) : ∃ a, a ≪ z ∧ {w | a ≪ w} ⊆ U := by sorry
