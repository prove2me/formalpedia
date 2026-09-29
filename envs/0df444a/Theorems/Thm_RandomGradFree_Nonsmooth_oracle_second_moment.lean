-- Prove2me | Theorems.Thm_RandomGradFree_Nonsmooth_oracle_second_moment
-- name    : RandomGradFree.Nonsmooth.oracle_second_moment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T08:04:04.057572+00:00
-- url     : https://prove2.me/theorems/a6e6cdf9-0d0c-41fa-95be-5d2167d23889
-- title:
--   Theorem 4.1 (34) — $\mathbb E_u \|g_\mu(x)\|_*^2 \le L_0^2(f)(n+4)^2$
-- statement:
--   Let $E$ be a real inner product space of dimension $n$, let $f : E \to \mathbb R$ be convex and Lipschitz continuous with constant $L_0 \ge 0$, and let $\mu > 0$. For a standard Gaussian direction $u$, the random gradient-free oracle $g_\mu(x) = \frac{f(x+\mu u)-f(x)}{\mu} Bu$ satisfies, for every $x \in E$,
--
--   $$
--   \mathbb E_u \|g_\mu(x)\|_*^2 \le L_0^2 (n+4)^2 .
--   $$
--
--   This second-moment bound is the variance term in the convergence analysis of the random search method: it replaces the squared norm of a subgradient in the classical projected subgradient analysis, at the price of the factor $(n+4)^2$.
--
--   **Formalization Note** With the inner product $\langle B\cdot,\cdot\rangle$, $\|g_\mu(x)\|_*$ equals the norm of $B^{-1}g_\mu(x) = \frac{f(x+\mu u)-f(x)}{\mu}u$, which is what is integrated. Convexity is kept because it is a hypothesis of the paper's Theorem 4.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 538, Theorem 4, part 1, Eq. (34)

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_oracle

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Nonsmooth

theorem oracle_second_moment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (L₀ : ℝ) (hL₀ : 0 ≤ L₀) (hLip : ∀ x y, |f x - f y| ≤ L₀ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 < μ) (x : E) :
    ∫ u, ‖oracle f μ x u‖ ^ 2 ∂(stdGaussian E)
      ≤ L₀ ^ 2 * ((Module.finrank ℝ E : ℝ) + 4) ^ 2 := by sorry

end RandomGradFree.Nonsmooth
