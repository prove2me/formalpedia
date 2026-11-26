-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_inverseLimit_coordinate_continuous
-- name    : Scott1972.ContinuousLattice.inverseLimit_coordinate_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:36:53.808141+00:00
-- url     : https://prove2.me/theorems/f0f0d800-867a-40a9-8051-a2ed12dd292f
-- title:
--   Continuous Lattice: inverse Limit coordinate continuous
-- statement:
--   Every coordinate projection from the explicit product/subspace inverse-limit topology is
--   continuous.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L116-L124
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L116-L124

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem Scott1972.ContinuousLattice.inverseLimit_coordinate_continuous (n : ℕ) :
    @Continuous (InverseLimit D P) (D n) (inverseLimitTopology D P)
      scottTopologicalSpace (fun x => x.1 n) := by sorry
