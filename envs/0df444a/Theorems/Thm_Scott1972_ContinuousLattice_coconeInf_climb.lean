-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_coconeInf_climb
-- name    : Scott1972.ContinuousLattice.coconeInf_climb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:38:25.174805+00:00
-- url     : https://prove2.me/theorems/e2795364-9bec-4499-9775-de9463a60ac6
-- title:
--   Continuous Lattice: cocone Inf climb
-- statement:
--   Climbing then applying `f` is constant: `f_m(i_{m-1}…iₙ x) = fₙ(x)`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L680-L686
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L680-L686

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

theorem Scott1972.ContinuousLattice.coconeInf_climb (f : ∀ n, ScottMap (D n) D')
    (hf : ∀ n x, f n x = f (n + 1) ((P n).incl x)) {n : ℕ} (x : D n) :
    ∀ {m : ℕ} (h : n ≤ m), f m (embLE D P h x) = f n x := by sorry
