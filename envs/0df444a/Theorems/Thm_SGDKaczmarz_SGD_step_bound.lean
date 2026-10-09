-- Prove2me | Theorems.Thm_SGDKaczmarz_SGD_step_bound
-- name    : SGDKaczmarz.SGD.step_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:26:23.127918+00:00
-- url     : https://prove2.me/theorems/a8b9aa65-7d14-4c63-805c-99434c97e329
-- title:
--   Proof of Theorem 2.1, p. 22 — pathwise bound on ‖x_k − x⋆ − γ∇f_i(x_k)‖² via Jensen and co-coercivity
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $g : \mathcal H \to \mathbb R$ a differentiable convex function (playing one component $f_i$) whose gradient is Lipschitz with constant $L_i \ge 0$. For all points $x$ (the current iterate $x_k$) and $x_\star$, and every real step $\gamma$,
--   $$\|x - x_\star - \gamma\nabla g(x)\|_2^2 \le \|x - x_\star\|_2^2 - 2\gamma\langle x - x_\star, \nabla g(x)\rangle + 2\gamma^2 L_i\langle x - x_\star, \nabla g(x) - \nabla g(x_\star)\rangle + 2\gamma^2\|\nabla g(x_\star)\|_2^2.$$
--
--   This is the first display of the proof of Theorem 2.1: one SGD step $x_{k+1} = x_k - \gamma\nabla f_i(x_k)$, bounded for every sampled index $i$ before any expectation is taken.
--
--   **Formalization Note** The bound is deterministic: it holds for every component and every point, so it is stated for a single function $g$ with constant $L_i$.
-- source:
--   Needell, Srebro & Ward, Stochastic gradient descent, weighted sampling, and the randomized Kaczmarz algorithm, arXiv:1310.5715v5, proof of Theorem 2.1 (Appendix A.2), first display, p. 22

import Mathlib

open scoped NNReal InnerProductSpace

namespace SGDKaczmarz.SGD

/-- Proof of Theorem 2.1 (Appendix A.2), p. 22, first display: the pathwise one-step bound for one
component `g = f_i` with Lipschitz constant `Li = L_i`, current point `x = x_k`. -/
theorem step_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (hg : Differentiable ℝ g) (hconv : ConvexOn ℝ Set.univ g) (Li : ℝ≥0)
    (hL : LipschitzWith Li (gradient g)) (x xstar : H) (γ : ℝ) :
    ‖x - xstar - γ • gradient g x‖ ^ 2
      ≤ ‖x - xstar‖ ^ 2 - 2 * γ * ⟪x - xstar, gradient g x⟫_ℝ
        + 2 * γ ^ 2 * Li * ⟪x - xstar, gradient g x - gradient g xstar⟫_ℝ
        + 2 * γ ^ 2 * ‖gradient g xstar‖ ^ 2 := by sorry

end SGDKaczmarz.SGD
