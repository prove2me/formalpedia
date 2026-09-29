-- Prove2me | Theorems.Thm_RandKaczmarz_expErrSq_succ
-- name    : RandKaczmarz.expErrSq_succ
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T16:17:03.571709+00:00
-- url     : https://prove2.me/theorems/58acf886-c23b-42f0-b798-e22f64ac958e
-- title:
--   Proof of Theorem 2: the conditioning (tower) identity for the $k$-step expectation
-- statement:
--   For all $A$, $b$, $x$, $x_0$ and $k$, with no hypotheses,
--   $$\mathbb{E}_{x_0}\|x_{k+1}-x\|_2^2=\sum_{i=1}^m p_i\,\mathbb{E}_{\mathrm{step}_i(x_0)}\|x_k-x\|_2^2,$$
--   where $\mathbb{E}_y$ is the expectation for the algorithm started at $y$. This is the tower identity: it splits off the first draw. The source instead conditions on the first $k-1$ draws; both play the same role in the induction.
-- source:
--   Strohmer & Vershynin, A randomized Kaczmarz algorithm with exponential convergence, arXiv:math/0702226v1 [math.NA], https://arxiv.org/abs/math/0702226 (published: J. Fourier Anal. Appl. 15 (2009), 262-278), p. 5, proof of Theorem 2, 'Now we take the expectation of both sides conditional upon the choice of the random vectors $Z_1,\dots,Z_{k-1}$'

import Definitions.Def_RandKaczmarz_core

open scoped InnerProductSpace ComplexConjugate
open WithLp Matrix

namespace RandKaczmarz

theorem expErrSq_succ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ)
    (x x₀ : EuclideanSpace ℂ (Fin n)) (k : ℕ) :
    expErrSq A b x (k + 1) x₀ = ∑ i, rowProb A i * expErrSq A b x k (step A b i x₀) := by sorry

end RandKaczmarz
