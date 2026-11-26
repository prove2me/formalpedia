-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_proposition_4_1
-- name    : Scott1972.ContinuousLattice.proposition_4_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:36:43.167497+00:00
-- url     : https://prove2.me/theorems/4f097bc3-f6f3-5b74-a93f-7b0044fb0982
-- title:
--   Continuous Lattice: proposition 4 1
-- statement:
--   **Scott 1972, Proposition 4.1.** The inverse limit is injective by the coordinatewise
--   Proposition 3.8/Lemma 3.9 construction; Theorem 2.12 then gives the continuous-lattice structure
--   on the existing componentwise complete lattice.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L272-L277
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L272-L277

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem Scott1972.ContinuousLattice.proposition_4_1 (hD : ∀ n, IsContinuousLattice (D n)) :
    IsContinuousLattice (InverseLimit D P) := by sorry
