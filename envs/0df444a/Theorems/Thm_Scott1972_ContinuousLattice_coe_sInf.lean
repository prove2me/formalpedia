-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_coe_sInf
-- name    : Scott1972.ContinuousLattice.coe_sInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:41:56.723534+00:00
-- url     : https://prove2.me/theorems/0a2cf77c-310b-57bf-b4d8-4018c6771298
-- title:
--   Continuous Lattice: coe s Inf
-- statement:
--   The Continuous Lattice construction uses the coe s Inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L148-L149
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L148-L149

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem Scott1972.ContinuousLattice.coe_sInf (S : Set (InverseLimit D P)) :
    ((sInf S : InverseLimit D P) : ∀ n, D n) = inverseLimitSInfCoe D P S := by sorry
