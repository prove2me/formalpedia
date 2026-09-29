-- Prove2me | Theorems.Thm_RandomGradFree_Accelerated_smoothing_gradient_lipschitz
-- name    : RandomGradFree.Accelerated.smoothing_gradient_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:08:13.932256+00:00
-- url     : https://prove2.me/theorems/5ef92ebb-29ee-4e1f-b358-70b32391f970
-- title:
--   Section 2, Eq. (12) — $f \in C^{1,1}$ implies $f_\mu \in C^{1,1}$ with $L_1(f_\mu) \le L_1(f)$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, and let $f : E \to \mathbb R$ be differentiable with $L_1$-Lipschitz gradient. Then for every $\mu \ge 0$ the Gaussian approximation $f_\mu$ is differentiable and its gradient is $L_1$-Lipschitz as well:
--
--   $$
--   \|\nabla f_\mu(x) - \nabla f_\mu(y)\|_* \le L_1\,\|x-y\|, \qquad x,y \in E.
--   $$
--
--   In the proof of Theorem 9 this gives the descent inequality for $f_\mu$ along the random step of the accelerated method.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 533, Section 2, third bullet, Eq. (12)

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

theorem smoothing_gradient_lipschitz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) :
    Differentiable ℝ (RandomGradFree.Shared.smoothing f μ) ∧
      ∀ x y, ‖gradient (RandomGradFree.Shared.smoothing f μ) x - gradient (RandomGradFree.Shared.smoothing f μ) y‖ ≤ L₁ * ‖x - y‖ := by sorry

end RandomGradFree.Accelerated
