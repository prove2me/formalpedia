-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_inverseLimit_t0Space
-- name    : Scott1972.ContinuousLattice.inverseLimit_t0Space
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:36:42.808796+00:00
-- url     : https://prove2.me/theorems/f64a2b8e-510f-5d7e-8bf2-8c39c2693f54
-- title:
--   Continuous Lattice: inverse Limit t0 Space
-- statement:
--   The explicit inverse-limit topology is `T₀`, since the inclusion into the product of the
--   stage Scott spaces is an embedding.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L202-L209
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L202-L209

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem Scott1972.ContinuousLattice.inverseLimit_t0Space :
    @T0Space (InverseLimit D P) (inverseLimitTopology D P) := by sorry
