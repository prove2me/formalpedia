-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_coconeInf_comp_embInf
-- name    : Scott1972.ContinuousLattice.coconeInf_comp_embInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:38:37.449785+00:00
-- url     : https://prove2.me/theorems/d392054c-8553-4d44-9427-d1f1e0decbba
-- title:
--   Continuous Lattice: cocone Inf comp emb Inf
-- statement:
--   **Scott 1972, Corollary 4.3 (factorization).** `fₙ = f∞ ∘ i_{n∞}`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L703-L714
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L703-L714

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
variable {D' : Type*} [CompleteLattice D']

theorem Scott1972.ContinuousLattice.coconeInf_comp_embInf (f : ∀ n, ScottMap (D n) D')
    (hf : ∀ n x, f n x = f (n + 1) ((P n).incl x)) (n : ℕ) (x : D n) :
    coconeInf D P f (embInf D P n x) = f n x := by sorry
