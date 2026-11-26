-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_embInf_le_succ
-- name    : Scott1972.ContinuousLattice.embInf_le_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:37:10.28681+00:00
-- url     : https://prove2.me/theorems/aeb6f967-13a2-4ff4-a606-26fc0bb13929
-- title:
--   Continuous Lattice: emb Inf le succ
-- statement:
--   The family `n ↦ i_{n∞}(xₙ)` is monotone (the lub defining `x` is monotone).
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L553-L558
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L553-L558

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem Scott1972.ContinuousLattice.embInf_le_succ (x : InverseLimit D P) (n : ℕ) :
    embInf D P n (x.1 n) ≤ embInf D P (n + 1) (x.1 (n + 1)) := by sorry
