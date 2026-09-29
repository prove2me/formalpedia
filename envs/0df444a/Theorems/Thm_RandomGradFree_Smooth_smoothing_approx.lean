-- Prove2me | Theorems.Thm_RandomGradFree_Smooth_smoothing_approx
-- name    : RandomGradFree.Smooth.smoothing_approx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T09:56:24.683516+00:00
-- url     : https://prove2.me/theorems/e62b4db9-7f49-4dcc-ba56-096c99d363bc
-- title:
--   Theorem 1 (19) — $|f_\mu(x) - f(x)| \le \frac{\mu^2}{2}L_1(f)\,n$ for $f\in C^{1,1}$
-- statement:
--   Let $E$ be a real inner product space of finite dimension $n$ and let $f : E \to \mathbb R$ be differentiable with $L_1$-Lipschitz gradient ($f \in C^{1,1}(E)$). Then for every $\mu \ge 0$ and every $x \in E$,
--
--   $$
--   |f_\mu(x) - f(x)| \le \frac{\mu^2}{2}\, L_1\, n .
--   $$
--
--   This is the quadratic-in-$\mu$ approximation guarantee for smooth functions; it is the source of the $\mu^2$ terms in the rates of the random gradient method.
--
--   **Formalization Note** $L_1$ is any constant for which the gradient-Lipschitz inequality holds (the paper's $L_1(f)$ is the best one; the bound is monotone in it).
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 534, Theorem 1, Eq. (19)

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Smooth

theorem smoothing_approx {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ)
    (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    |RandomGradFree.Shared.smoothing f μ x - f x| ≤ μ ^ 2 / 2 * L₁ * Module.finrank ℝ E := by sorry

end RandomGradFree.Smooth
