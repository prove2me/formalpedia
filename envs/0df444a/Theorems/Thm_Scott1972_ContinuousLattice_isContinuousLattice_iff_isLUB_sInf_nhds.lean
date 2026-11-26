-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_isContinuousLattice_iff_isLUB_sInf_nhds
-- name    : Scott1972.ContinuousLattice.isContinuousLattice_iff_isLUB_sInf_nhds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:31:04.693955+00:00
-- url     : https://prove2.me/theorems/68ad2388-5cb5-5c99-92b0-6a17b82246b2
-- title:
--   Continuous Lattice: is Continuous Lattice iff is LUB s Inf nhds
-- statement:
--   **Scott 1972, Proposition 2.4.** A complete lattice is continuous iff every element is the
--   supremum of the infima of its open neighbourhoods: `y = ⊔ {⊓U : y ∈ U open}`. This is Scott's
--   alternate form of Definition 2.3.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L227-L246
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/WayBelow.lean#L227-L246

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import Definitions.Def_Scott1972_ContinuousLattice_WayBelow
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
variable {D : Type u} [CompleteLattice D]

theorem Scott1972.ContinuousLattice.isContinuousLattice_iff_isLUB_sInf_nhds :
    IsContinuousLattice D ↔
      ∀ y : D, IsLUB {a : D | ∃ U, ScottOpen U ∧ y ∈ U ∧ a = sInf U} y := by sorry
