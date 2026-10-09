-- Prove2me | Theorems.Thm_SGDKaczmarz_SGD_eq_A_1
-- name    : SGDKaczmarz.SGD.eq_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:26:21.812319+00:00
-- url     : https://prove2.me/theorems/f200da78-4bd7-47c3-931f-1d99643799d6
-- title:
--   (A.1), p. 21 — (1/2L)‖∇f(x) − ∇f(x⋆)‖² ≤ f(x) − f(x⋆) at a minimizer x⋆ of an L-smooth f
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $f : \mathcal H \to \mathbb R$ a differentiable function whose gradient is Lipschitz with constant $L > 0$:
--   $$\|\nabla f(x) - \nabla f(y)\|_2 \le L\|x - y\|_2 \quad \text{for all } x, y.$$
--   If $x_\star$ is a global minimizer of $f$, then for every $x \in \mathcal H$
--   $$\frac{1}{2L}\|\nabla f(x) - \nabla f(x_\star)\|_2^2 \le f(x) - f(x_\star).$$
--
--   This is inequality (A.1) of the paper, which the proof of the co-coercivity Lemma A.1 applies to two auxiliary convex functions.
--
--   **Formalization Note** The page writes (A.1) as a chain whose middle term adds $\langle x - x_\star, \nabla f(x_\star)\rangle$, which is $0$ at a minimizer; only the outer inequality is stated. The hypothesis $L > 0$ is needed because the page divides by $L$. Convexity is not assumed: the inequality holds at any global minimizer.
-- source:
--   Needell, Srebro & Ward, Stochastic gradient descent, weighted sampling, and the randomized Kaczmarz algorithm, arXiv:1310.5715v5, proof of Lemma A.1 (Appendix A.1), (A.1), p. 21

import Mathlib

open scoped NNReal InnerProductSpace

namespace SGDKaczmarz.SGD

/-- (A.1), proof of Lemma A.1, p. 21 (outer inequality): if `∇f` is `L`-Lipschitz and `x⋆`
minimizes `f`, then `(1/2L)‖∇f(x) − ∇f(x⋆)‖² ≤ f(x) − f(x⋆)`. -/
theorem eq_A_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hf : Differentiable ℝ f) (L : ℝ≥0) (hL0 : 0 < L)
    (hL : LipschitzWith L (gradient f)) (xstar : H) (hmin : ∀ y, f xstar ≤ f y) (x : H) :
    1 / (2 * (L : ℝ)) * ‖gradient f x - gradient f xstar‖ ^ 2 ≤ f x - f xstar := by sorry

end SGDKaczmarz.SGD
