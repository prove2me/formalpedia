-- Prove2me | Theorems.Thm_RandKaczmarz_randomized_kaczmarz_lower_bound_norm
-- name    : RandKaczmarz.randomized_kaczmarz_lower_bound_norm
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T16:18:46.223688+00:00
-- url     : https://prove2.me/theorems/dba24714-5e18-403c-bfb0-1393b599a49f
-- title:
--   Proof of Theorem 3: the lower bound in $\|\cdot\|_2$, as the source's argument establishes it
-- statement:
--   Let $A\in\mathbb{C}^{m\times n}$ have full rank, $m\ge n\ge1$, and $Ax=b$. Some $x_0\ne x$ satisfies, for every $k\ge1$,
--   $$\mathbb{E}\,\|x_k-x\|_2\ge\Bigl(1-\frac{2k}{\kappa(A)^2}\Bigr)\|x_0-x\|_2$$
--   (unsquared norm). This is what the source's proof of Theorem 3 actually shows (last display, p. 8). It is weaker than the squared form, because $\|x_k-x\|_2\le\|x_0-x\|_2$ on every run.
--
--   **Formalization Note** $\mathbb{E}\|x_k-x\|_2$ is written out as the same finite sum as `expErrSq`, without the square. The condition $x_0\ne x$ excludes the trivial witness $x_0=x$.
-- source:
--   Strohmer & Vershynin, A randomized Kaczmarz algorithm with exponential convergence, arXiv:math/0702226v1 [math.NA], https://arxiv.org/abs/math/0702226 (published: J. Fourier Anal. Appl. 15 (2009), 262-278), p. 8, the final display of the proof of Theorem 3

import Definitions.Def_RandKaczmarz_core

open scoped InnerProductSpace ComplexConjugate
open WithLp Matrix

namespace RandKaczmarz

theorem randomized_kaczmarz_lower_bound_norm {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ) (hA : Function.Injective (mulVecE A))
    (x : EuclideanSpace ℂ (Fin n)) (hx : A *ᵥ ofLp x = b) :
    ∃ x₀ : EuclideanSpace ℂ (Fin n), x₀ ≠ x ∧ ∀ k : ℕ, 1 ≤ k →
      (1 - 2 * (k : ℝ) / scaledCond A ^ 2) * ‖x₀ - x‖
        ≤ ∑ p : Fin k → Fin m,
            pathProb A (List.ofFn p) * ‖runSteps A b (List.ofFn p) x₀ - x‖ := by sorry

end RandKaczmarz
