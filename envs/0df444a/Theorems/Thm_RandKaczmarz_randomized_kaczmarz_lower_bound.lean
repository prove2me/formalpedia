-- Prove2me | Theorems.Thm_RandKaczmarz_randomized_kaczmarz_lower_bound
-- name    : RandKaczmarz.randomized_kaczmarz_lower_bound
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T16:19:14.350905+00:00
-- url     : https://prove2.me/theorems/0bd97492-58a1-4c0b-ac85-3e6e00c481fe
-- title:
--   Theorem 3: $\mathbb{E}\|x_k-x\|_2^2 \ge (1-2k/\kappa(A)^2)\|x_0-x\|_2^2$ for some $x_0$
-- statement:
--   **Theorem 3.** Let $A\in\mathbb{C}^{m\times n}$ have full rank, $m\ge n\ge1$, and $Ax=b$. Some $x_0\ne x$ satisfies, for every $k\ge1$,
--   $$\mathbb{E}\,\|x_k-x\|_2^2\ge\Bigl(1-\frac{2k}{\kappa(A)^2}\Bigr)\|x_0-x\|_2^2 .$$
--   So the exponent in Theorem 2 is sharp up to a constant.
--
--   **Warning** The source's proof does not reach this statement. It proves the unsquared version (milestone *Theorem 3 (norm form)*) and then cites Jensen's inequality, which goes the wrong way. Its estimates give this statement with $4$ in place of $2$; getting $2$ needs a new argument.
--
--   **Formalization Note** The condition $x_0\ne x$ excludes the trivial witness $x_0=x$. The source's witness is $x$ plus a unit vector attaining $\sigma_{\min}(A)$.
-- source:
--   Strohmer & Vershynin, A randomized Kaczmarz algorithm with exponential convergence, arXiv:math/0702226v1 [math.NA], https://arxiv.org/abs/math/0702226 (published: J. Fourier Anal. Appl. 15 (2009), 262-278), p. 7, Theorem 3 and eq. (12); proof on pp. 7-8, eq. (13)-(17)

import Definitions.Def_RandKaczmarz_core

open scoped InnerProductSpace ComplexConjugate
open WithLp Matrix

namespace RandKaczmarz

theorem randomized_kaczmarz_lower_bound {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ) (hA : Function.Injective (mulVecE A))
    (x : EuclideanSpace ℂ (Fin n)) (hx : A *ᵥ ofLp x = b) :
    ∃ x₀ : EuclideanSpace ℂ (Fin n), x₀ ≠ x ∧ ∀ k : ℕ, 1 ≤ k →
      (1 - 2 * (k : ℝ) / scaledCond A ^ 2) * ‖x₀ - x‖ ^ 2 ≤ expErrSq A b x k x₀ := by sorry

end RandKaczmarz
