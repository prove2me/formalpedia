-- Prove2me | Theorems.Thm_RandomGradFree_Smooth_smoothing_hasGradient
-- name    : RandomGradFree.Smooth.smoothing_hasGradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T09:21:02.636986+00:00
-- url     : https://prove2.me/theorems/470ad447-d010-41b1-aa0e-af8b60446b0a
-- title:
--   Section 2, Eq. (21) — $\nabla f_\mu(x) = \mathbb E_u \frac{f(x+\mu u)-f(x)}{\mu}Bu$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $f : E \to \mathbb R$ differentiable with $L_1$-Lipschitz gradient, and $\mu > 0$. Then the Gaussian approximation $f_\mu$ is differentiable at every $x \in E$, and its gradient is the expected finite-difference oracle:
--
--   $$
--   \nabla f_\mu(x) = \mathbb E_u\!\left[\frac{f(x+\mu u) - f(x)}{\mu}\, u\right] = \frac1\kappa\int_E \frac{f(x+\mu u)-f(x)}{\mu}\, e^{-\frac12\|u\|^2}\, u\, du .
--   $$
--
--   This identity says that the random oracle $g_\mu$ is an unbiased estimator of $\nabla f_\mu$, so the random gradient method is a stochastic gradient method for $f_\mu$.
--
--   **Formalization Note** The paper's formula has $Bu$ (a dual vector); after identifying $E^*$ with $E$ via the inner product this is the vector $u$. The paper asks only that $f$ be continuous enough to differentiate under the integral and leaves integrability implicit; here $f \in C^{1,1}$ (the setting of Theorem 8) guarantees it.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), pp. 534-535, Section 2, Eq. (21)

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing
import Definitions.Def_RandomGradFree_Shared_oracle

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Smooth

theorem smoothing_hasGradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ)
    (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 < μ) (x : E) :
    HasGradientAt (RandomGradFree.Shared.smoothing f μ) (∫ u, RandomGradFree.Shared.oracle f μ x u ∂(stdGaussian E)) x := by sorry

end RandomGradFree.Smooth
