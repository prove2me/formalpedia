-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_sInf_wayBelow
-- name    : Scott1972.ContinuousLattice.sInf_wayBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:48.884892+00:00
-- url     : https://prove2.me/theorems/6d5cc9e4-66eb-4596-b7d2-754d12f428a5
-- title:
--   Continuous Lattice: s Inf way Below
-- statement:
--   The infimum of a Scott-open neighbourhood of `y` is way below `y`: the open set is itself
--   the required witness. Scott uses this in moving between Definition 2.3 and Proposition 2.4.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L220-L222
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L220-L222

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.sInf_wayBelow {U : Set D} (hU : ScottOpen U) {y : D} (hy : y ∈ U) :
    sInf U ≪ y := by sorry
