-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_coconeInf_descend
-- name    : Scott1972.ContinuousLattice.coconeInf_descend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:38:44.728439+00:00
-- url     : https://prove2.me/theorems/4f44bdbf-4e4e-4ca7-bfa5-b1d6d3cf6f20
-- title:
--   Continuous Lattice: cocone Inf descend
-- statement:
--   Descending then applying `f` only decreases: `f_m(j_m…j_{n-1} x) ⊑ fₙ(x)`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L689-L700
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L689-L700

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

theorem Scott1972.ContinuousLattice.coconeInf_descend (f : ∀ n, ScottMap (D n) D')
    (hf : ∀ n x, f n x = f (n + 1) ((P n).incl x)) {m : ℕ} :
    ∀ {n : ℕ} (h : m ≤ n) (x : D n), f m (projLE D P h x) ≤ f n x := by sorry
