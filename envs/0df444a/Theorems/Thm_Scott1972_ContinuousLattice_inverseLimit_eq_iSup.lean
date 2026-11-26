-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_inverseLimit_eq_iSup
-- name    : Scott1972.ContinuousLattice.inverseLimit_eq_iSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:36:46.612804+00:00
-- url     : https://prove2.me/theorems/11e3d937-9739-46b3-8d07-b6c88af81c1c
-- title:
--   Continuous Lattice: inverse Limit eq i Sup
-- statement:
--   **Scott 1972, §4.** Each `x ∈ D_∞` is the (monotone) lub of its projections:
--   `x = ⨆ₙ i_{n∞}(xₙ)`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L566-L584
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L566-L584

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem Scott1972.ContinuousLattice.inverseLimit_eq_iSup (x : InverseLimit D P) :
    x = ⨆ n, embInf D P n (x.1 n) := by sorry
