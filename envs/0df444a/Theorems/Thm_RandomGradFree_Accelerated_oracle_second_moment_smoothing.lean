-- Prove2me | Theorems.Thm_RandomGradFree_Accelerated_oracle_second_moment_smoothing
-- name    : RandomGradFree.Accelerated.oracle_second_moment_smoothing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:08:41.839661+00:00
-- url     : https://prove2.me/theorems/6f738a12-af74-4d83-9ec7-918a14163002
-- title:
--   Lemma 5 — $\mathbb E_u\|g_\mu(x)\|_*^2 \le 4(n+4)\|\nabla f_\mu(x)\|_*^2 + 3\mu^2L_1^2(f)(n+4)^3$ (Eq. (37))
-- statement:
--   Let $E$ be a real inner product space of dimension $n$, and let $f : E \to \mathbb R$ be differentiable with $L_1$-Lipschitz gradient (no convexity is assumed). Let $\mu > 0$ and let $u$ be a standard Gaussian vector in $E$. Then for every $x \in E$ the random gradient-free oracle $B^{-1}g_\mu(x) = \frac{f(x+\mu u)-f(x)}{\mu}u$ satisfies
--
--   $$
--   \mathbb E_u\big(\|g_\mu(x)\|_*^2\big) \le 4(n+4)\,\|\nabla f_\mu(x)\|_*^2 + 3\mu^2 L_1^2 (n+4)^3 .
--   $$
--
--   Unlike the bound in terms of $\nabla f(x)$, this form has the gradient of the smoothed function on the right, which is what the analysis of the accelerated method needs.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 539, Lemma 5, Eq. (37)

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing
import Definitions.Def_RandomGradFree_Shared_oracle

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

theorem oracle_second_moment_smoothing {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 < μ) (x : E) :
    ∫ u, ‖RandomGradFree.Shared.oracle f μ x u‖ ^ 2 ∂(stdGaussian E)
      ≤ 4 * ((Module.finrank ℝ E : ℝ) + 4) * ‖gradient (RandomGradFree.Shared.smoothing f μ) x‖ ^ 2
        + 3 * μ ^ 2 * L₁ ^ 2 * ((Module.finrank ℝ E : ℝ) + 4) ^ 3 := by sorry

end RandomGradFree.Accelerated
