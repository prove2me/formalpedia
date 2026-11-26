-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLattice_sSup_wayBelow
-- name    : Scott1972.ContinuousLattice.IsContinuousLattice.sSup_wayBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:28:07.338227+00:00
-- url     : https://prove2.me/theorems/c7fedc00-fc6e-4bcd-b664-52c44a5534b5
-- title:
--   Is Continuous Lattice: s Sup way Below
-- statement:
--   In a continuous lattice, `y` is the actual supremum of `{x | x ≪ y}`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L159-L161
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L159-L161

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.IsContinuousLattice.sSup_wayBelow (h : IsContinuousLattice D) (y : D) :
    sSup {x | x ≪ y} = y := by sorry
