-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_inverseLimit_isInjectiveSpace
-- name    : Scott1972.ContinuousLattice.inverseLimit_isInjectiveSpace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:36:47.164091+00:00
-- url     : https://prove2.me/theorems/2bc81ea9-d80a-5412-a0cb-e1b4150e4d97
-- title:
--   Continuous Lattice: inverse Limit is Injective Space
-- statement:
--   **Scott 1972, Proposition 4.1 (injectivity step).** Coordinatewise maximal extensions
--   assemble to an extension into the inverse limit. Lemma 3.9 is exactly what supplies compatibility
--   of adjacent coordinates.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L234-L267
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L234-L267

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem Scott1972.ContinuousLattice.inverseLimit_isInjectiveSpace (hD : ∀ n, IsContinuousLattice (D n)) :
    @IsInjectiveSpace.{u, u} (InverseLimit D P) (inverseLimitTopology D P) := by sorry
