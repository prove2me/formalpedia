-- Prove2me | Theorems.Thm_RandKaczmarz_randomized_kaczmarz_exp_convergence
-- name    : RandKaczmarz.randomized_kaczmarz_exp_convergence
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T16:17:29.528223+00:00
-- url     : https://prove2.me/theorems/e4ddf89f-9105-4844-886c-76571901bd66
-- title:
--   Theorem 2: $\mathbb{E}\|x_k-x\|_2^2 \le (1-\kappa(A)^{-2})^k \|x_0-x\|_2^2$
-- statement:
--   **Theorem 2.** Let $A\in\mathbb{C}^{m\times n}$ have full rank, $m\ge n\ge1$, and $Ax=b$. Run Algorithm 1 from any $x_0$: each step draws row $i$ independently with probability $\|a_i\|_2^2/\|A\|_F^2$ and projects onto that equation's hyperplane. Then for every $k\ge0$,
--   $$\mathbb{E}\,\|x_k-x\|_2^2\le\bigl(1-\kappa(A)^{-2}\bigr)^k\,\|x_0-x\|_2^2,$$
--   where $\kappa(A)=\|A\|_F/\sigma_{\min}(A)$. The rate does not depend on $m$.
--
--   **Formalization Note** Full rank is stated as injectivity of $z\mapsto Az$. The expectation is the finite sum over the $m^k$ row sequences.
-- source:
--   Strohmer & Vershynin, A randomized Kaczmarz algorithm with exponential convergence, arXiv:math/0702226v1 [math.NA], https://arxiv.org/abs/math/0702226 (published: J. Fourier Anal. Appl. 15 (2009), 262-278), p. 4, Theorem 2 and eq. (5); the algorithm being analysed is Algorithm 1 and eq. (4), p. 4

import Definitions.Def_RandKaczmarz_core

open scoped InnerProductSpace ComplexConjugate
open WithLp Matrix

namespace RandKaczmarz

theorem randomized_kaczmarz_exp_convergence {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ)
    (hA : Function.Injective (mulVecE A))
    (x x₀ : EuclideanSpace ℂ (Fin n)) (hx : A *ᵥ ofLp x = b) (k : ℕ) :
    expErrSq A b x k x₀ ≤ (1 - (scaledCond A ^ 2)⁻¹) ^ k * ‖x₀ - x‖ ^ 2 := by sorry

end RandKaczmarz
