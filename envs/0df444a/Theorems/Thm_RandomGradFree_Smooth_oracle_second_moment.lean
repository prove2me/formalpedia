-- Prove2me | Theorems.Thm_RandomGradFree_Smooth_oracle_second_moment
-- name    : RandomGradFree.Smooth.oracle_second_moment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T09:12:18.583034+00:00
-- url     : https://prove2.me/theorems/2500b1c5-f52f-4485-bd6d-1ece23ce0672
-- title:
--   Theorem 4.2 (35) — second moments of $g_\mu$ and $\hat g_\mu$ for $f\in C^{1,1}$
-- statement:
--   Let $E$ be a real inner product space of finite dimension $n$, $u$ a standard Gaussian vector in $E$, and $f : E \to \mathbb R$ convex, differentiable, with $L_1$-Lipschitz gradient. Let $\mu > 0$ and $x \in E$, and let $g_\mu(x)$, $\hat g_\mu(x)$ be the oracles of (30). Then
--
--   $$
--   \begin{aligned}
--   \mathbb E_u\big(\|g_\mu(x)\|_*^2\big) &\le \frac{\mu^2}{2}L_1^2(n+6)^3 + 2(n+4)\|\nabla f(x)\|_*^2,\\
--   \mathbb E_u\big(\|\hat g_\mu(x)\|_*^2\big) &\le \frac{\mu^2}{8}L_1^2(n+6)^3 + 2(n+4)\|\nabla f(x)\|_*^2.
--   \end{aligned}
--   $$
--
--   The first inequality is the variance bound used in the complexity analysis of the random gradient method $\mathcal{RG}_\mu$ (Theorem 8).
--
--   **Formalization Note** The convexity hypothesis of Theorem 4's preamble is kept, as in the paper's statement. $\|g_\mu(x)\|_* = \|B^{-1}g_\mu(x)\|$. Both second moments are genuine integrals: for $f \in C^{1,1}$ the finite differences are bounded by $\|\nabla f(x)\|\|u\| + \frac{\mu}{2}L_1\|u\|^2$.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 538, Theorem 4, part 2, Eq. (35)

import Mathlib
import Definitions.Def_RandomGradFree_Shared_oracle
import Definitions.Def_RandomGradFree_Smooth_symOracle

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Smooth

theorem oracle_second_moment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 < μ) (x : E) :
    ∫ u, ‖RandomGradFree.Shared.oracle f μ x u‖ ^ 2 ∂(stdGaussian E)
        ≤ μ ^ 2 / 2 * L₁ ^ 2 * ((Module.finrank ℝ E : ℝ) + 6) ^ 3
          + 2 * ((Module.finrank ℝ E : ℝ) + 4) * ‖gradient f x‖ ^ 2 ∧
      ∫ u, ‖symOracle f μ x u‖ ^ 2 ∂(stdGaussian E)
        ≤ μ ^ 2 / 8 * L₁ ^ 2 * ((Module.finrank ℝ E : ℝ) + 6) ^ 3
          + 2 * ((Module.finrank ℝ E : ℝ) + 4) * ‖gradient f x‖ ^ 2 := by sorry

end RandomGradFree.Smooth
