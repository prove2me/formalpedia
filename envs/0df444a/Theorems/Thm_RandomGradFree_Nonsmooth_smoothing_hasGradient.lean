-- Prove2me | Theorems.Thm_RandomGradFree_Nonsmooth_smoothing_hasGradient
-- name    : RandomGradFree.Nonsmooth.smoothing_hasGradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:56:34.874688+00:00
-- url     : https://prove2.me/theorems/58633292-e96f-46c9-9649-089f1d71d9ee
-- title:
--   Section 2, Eq. (21) — $\nabla f_\mu(x) = \mathbb E_u \frac{f(x+\mu u)-f(x)}{\mu} Bu$
-- statement:
--   Let $f : E \to \mathbb R$ be Lipschitz continuous with constant $L_0 \ge 0$ and let $\mu > 0$. Then the Gaussian smoothing $f_\mu$ is differentiable at every $x \in E$, and its gradient is the expectation of the finite-difference oracle:
--
--   $$
--   \nabla f_\mu(x) = \mathbb E_u\!\left[\frac{f(x+\mu u) - f(x)}{\mu}\, u\right].
--   $$
--
--   In other words, the random oracle $g_\mu(x)$ is an unbiased estimator of $\nabla f_\mu(x)$; this is the identity that turns the random search method into a stochastic gradient method for $f_\mu$.
--
--   **Formalization Note** "Differentiable with this gradient" is Mathlib's `HasGradientAt`, with the gradient taken with respect to the inner product of $E$ (the paper's $\langle B\cdot,\cdot\rangle$, so the paper's $B^{-1}\nabla f_\mu(x)$). The paper assumes only that $f$ has directional derivatives and differentiates under the integral sign; Lipschitz continuity is assumed here, which justifies that step and is the setting of Theorem 6.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), pp. 534-535, Section 2, Eq. (21)

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing
import Definitions.Def_RandomGradFree_Nonsmooth_oracle

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Nonsmooth

theorem smoothing_hasGradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₀ : ℝ) (hL₀ : 0 ≤ L₀) (hLip : ∀ x y, |f x - f y| ≤ L₀ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 < μ) (x : E) :
    HasGradientAt (RandomGradFree.Shared.smoothing f μ) (∫ u, oracle f μ x u ∂(stdGaussian E)) x := by sorry

end RandomGradFree.Nonsmooth
