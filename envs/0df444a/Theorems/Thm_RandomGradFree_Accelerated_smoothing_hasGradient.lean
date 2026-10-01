-- Prove2me | Theorems.Thm_RandomGradFree_Accelerated_smoothing_hasGradient
-- name    : RandomGradFree.Accelerated.smoothing_hasGradient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:09:13.709827+00:00
-- url     : https://prove2.me/theorems/f4f0c33d-027c-4b3b-a010-eff23b1d8b4d
-- title:
--   Section 2, Eq. (21) — $\nabla f_\mu(x) = \mathbb E_u\, g_\mu(x)$ for $\mu > 0$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, let $f : E \to \mathbb R$ be differentiable with $L_1$-Lipschitz gradient, and let $\mu > 0$. Then the Gaussian approximation $f_\mu$ is differentiable at every $x \in E$, and its gradient is the expectation of the random gradient-free oracle:
--
--   $$
--   \nabla f_\mu(x) = \frac{1}{\kappa}\int_E \frac{f(x+\mu u) - f(x)}{\mu}\, e^{-\frac12\|u\|^2}\, Bu\,du = \mathbb E_u\big(g_\mu(x)\big).
--   $$
--
--   Thus $g_\mu(x)$ is an unbiased estimate of $\nabla f_\mu(x)$; this is the identity used when the expectation over $u_k$ is taken in the proof of Theorem 9.
--
--   **Formalization Note** The statement is `HasGradientAt` of $f_\mu$ at $x$ with gradient the Bochner integral of the ($B^{-1}$-applied) oracle against `stdGaussian E`. The paper states differentiability for any positive $\mu$; the $C^{1,1}$ hypothesis of this mission guarantees the integrals exist.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), pp. 534-535, Section 2, Eq. (21)

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing
import Definitions.Def_RandomGradFree_Shared_oracle

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

theorem smoothing_hasGradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 < μ) (x : E) :
    HasGradientAt (RandomGradFree.Shared.smoothing f μ) (∫ u, RandomGradFree.Shared.oracle f μ x u ∂(stdGaussian E)) x := by sorry

end RandomGradFree.Accelerated
