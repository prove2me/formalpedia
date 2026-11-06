-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_lemma_A_1
-- name    : SparseSDP.TwoSided.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:54:52.03036+00:00
-- url     : https://prove2.me/theorems/94338189-620b-427f-9ec7-eb3e75966096
-- title:
--   Lemma A.1, p. 68 — realification preserves payoffs, spectra and the gap
-- statement:
--   Let $A_1,\dots,A_m\in\mathbb C^{n\times n}$ be Hermitian and $R,r>0$.
--
--   1. For every real symmetric $Y\in R\mathcal S_{2n}$, the matrix $X=\Psi(Y)$ lies in $R\mathcal S_n$ and $\langle A_j,X\rangle=\langle\Phi(A_j),Y\rangle$ for every $j$. Conversely, every $X\in R\mathcal S_n$ has the real embedding $Y=\tfrac12\Phi(X)\in R\mathcal S_{2n}$ with $\Psi(Y)=X$.
--   2. For every $y\in\mathbb R^m$,
--   $$
--   \lambda_{\max}\Big(\sum_jy_j\Phi(A_j)\Big)=\lambda_{\max}\Big(\sum_jy_jA_j\Big).
--   $$
--   3. The real and Hermitian games have the same saddle-point value, and $\mathrm{Gap}_{\mathbb R}(Y,y)=\mathrm{Gap}_{\mathbb C}(\Psi(Y),y)$ for every real symmetric $Y\in R\mathcal S_{2n}$ and $y\in r\Delta_m$.
--
--   So the solver for real symmetric matrices serves Hermitian inputs.
--
--   Differences from the source:
--   - encoding: the saddle-point value → `saddleValue` in the max–min form of Eq. (34); reason: both forms agree by Eq. (34)
--   - encoding: block matrices of size $2n$ → matrices on `Fin (n + n)` via `finSumFinEquiv`; reason: Lean indexing; same matrices
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Lemma A.1, p. 68, Eqs. (379)–(381)

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_realify

open Matrix
open scoped ComplexOrder

namespace SparseSDP.TwoSided

/-- **Lemma A.1** (SDP Gap Preservation Under "Realification"), p. 68.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Lemma A.1, p. 68.

Radii `R, r > 0` as in §2.5. Items: (1) `Ψ` maps `RS_{2n}` into `RSₙ`, preserving every payoff
(Eq. (379)), and `½Φ(X)` is a preimage of each `X ∈ RSₙ` in `RS_{2n}`; (2) Eq. (380); (3) equal game
values, and Eq. (381). -/
theorem lemma_A_1 {n m : ℕ} [NeZero m] (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (R r : ℝ)
    (hA : ∀ j, (A j).IsHermitian) (hR : 0 < R) (hr : 0 < r) :
    (∀ Y ∈ (Spect R : Set (Matrix (Fin (n + n)) (Fin (n + n)) ℝ)),
      derealify Y ∈ (Spect R : Set (Matrix (Fin n) (Fin n) ℂ)) ∧
      ∀ j, hs (A j) (derealify Y) = hs (realify (A j)) Y) ∧
    (∀ X ∈ (Spect R : Set (Matrix (Fin n) (Fin n) ℂ)),
      ((1 / 2 : ℝ) • realify X) ∈ (Spect R : Set (Matrix (Fin (n + n)) (Fin (n + n)) ℝ)) ∧
      derealify ((1 / 2 : ℝ) • realify X) = X) ∧
    (∀ y : Fin m → ℝ, lamMax (adj (fun j => realify (A j)) y) = lamMax (adj A y)) ∧
    saddleValue (fun j => realify (A j)) R r = saddleValue A R r ∧
    (∀ Y ∈ (Spect R : Set (Matrix (Fin (n + n)) (Fin (n + n)) ℝ)), ∀ y ∈ Simplex m r,
      gap (fun j => realify (A j)) R r Y y = gap A R r (derealify Y) y) := by sorry

end SparseSDP.TwoSided
