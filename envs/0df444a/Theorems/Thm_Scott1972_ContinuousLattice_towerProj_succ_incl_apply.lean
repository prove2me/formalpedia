-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_towerProj_succ_incl_apply
-- name    : Scott1972.ContinuousLattice.towerProj_succ_incl_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:46:50.481114+00:00
-- url     : https://prove2.me/theorems/3ba6f5de-22fb-4a35-b72c-d98a1a712083
-- title:
--   Continuous Lattice: tower Proj succ incl apply
-- statement:
--   **Scott 1972, recursion before Theorem 4.4 (from Proposition 3.7).**
--   `i_{n+1}(x) = iₙ ∘ x ∘ jₙ`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaceTower.lean#L213-L215
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaceTower.lean#L213-L215

import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Homeomorph.Defs
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaceTower
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
universe u
attribute [instance] CLat.str
variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

theorem Scott1972.ContinuousLattice.towerProj_succ_incl_apply (n : ℕ) (x : towerType D₀ (n + 1)) (y : towerType D₀ (n + 1)) :
    ((towerProj D₀ j₀ (n + 1)).incl x) y
      = (towerProj D₀ j₀ n).incl (x ((towerProj D₀ j₀ n).retr y)) := by sorry
