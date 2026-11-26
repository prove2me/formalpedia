-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_corollary_4_3
-- name    : Scott1972.ContinuousLattice.corollary_4_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:42:51.351685+00:00
-- url     : https://prove2.me/theorems/92ff7d60-219c-54e1-991a-c0b0a5bc93a2
-- title:
--   Continuous Lattice: corollary 4 3
-- statement:
--   **Scott 1972, Corollary 4.3.** Within complete lattices, `D_∞` is also the *direct* limit of
--   the `Dₙ` along the embeddings `iₙ`: for every compatible cocone `fₙ : Dₙ → D'` (continuous, with
--   `fₙ = f_{n+1} ∘ iₙ`) there is a **unique** continuous `f∞ : D_∞ → D'` with `fₙ = f∞ ∘ i_{n∞}`,
--   namely `f∞(x) = ⨆ₙ fₙ(xₙ)`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L748-L762
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/InverseLimits.lean#L748-L762

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

theorem Scott1972.ContinuousLattice.corollary_4_3 (f : ∀ n, ScottMap (D n) D')
    (hf : ∀ n x, f n x = f (n + 1) ((P n).incl x)) :
    ∃! g : ScottMap (InverseLimit D P) D', ∀ n x, f n x = g (embInf D P n x) := by sorry
