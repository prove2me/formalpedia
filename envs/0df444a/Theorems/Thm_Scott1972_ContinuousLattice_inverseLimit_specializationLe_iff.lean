-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_inverseLimit_specializationLe_iff
-- name    : Scott1972.ContinuousLattice.inverseLimit_specializationLe_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:37:03.896923+00:00
-- url     : https://prove2.me/theorems/2b90571b-fbc1-4a1a-85f7-6c27f6e7febf
-- title:
--   Continuous Lattice: inverse Limit specialization Le iff
-- statement:
--   The specialization order of the explicit inverse-limit topology is the componentwise order.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L212-L229
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L212-L229

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem Scott1972.ContinuousLattice.inverseLimit_specializationLe_iff (x y : InverseLimit D P) :
    @SpecializationLe (InverseLimit D P) (inverseLimitTopology D P) x y ↔ x ≤ y := by sorry
