-- Prove2me | Theorems.Thm_SAARate_Sharp_dirDeriv_ge_eps_norm
-- name    : SAARate.Sharp.dirDeriv_ge_eps_norm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:54.278689+00:00
-- url     : https://prove2.me/theorems/4ed96d8e-8420-4714-a96d-20e722431f96
-- title:
--   p. 4 (after (2.3)) — (2.3) implies g′(x̄, d) ≥ ε‖d‖ for some ε > 0 and all d ∈ T_Θ(x̄)
-- statement:
--   Let $g:\mathbb R^m\to\mathbb R$ be convex, let $\Theta\subseteq\mathbb R^m$ be convex, let $\bar x\in\Theta$, and suppose that
--   $$
--   g'(\bar x,d)>0\qquad\forall\, d\in T_\Theta(\bar x)\setminus\{0\}. \tag{2.3}
--   $$
--   Then there is $\varepsilon>0$ such that
--   $$
--   g'(\bar x,d)\ \ge\ \varepsilon\,\|d\|\qquad\forall\, d\in T_\Theta(\bar x).
--   $$
--
--   Here $g'(\bar x,d)$ is the directional derivative of $g$ at $\bar x$ in direction $d$ and $T_\Theta(\bar x)$ is the tangent cone to $\Theta$ at $\bar x$. Positivity on nonzero tangent directions is thereby upgraded to a uniform linear lower bound; on the unit sphere it gives $f'(\bar x,d)\ge\varepsilon$, the margin the proof of Theorem 2.1 needs before passing to the sample average.
--
--   **Formalization Note.** Stated for an arbitrary finite convex $g$ (the page states it for $f$). The tangent cone is Mathlib's `posTangentConeAt Θ x̄`, the closure of $\mathbb R_+(\Theta-\bar x)$ for convex $\Theta$. At $d=0$ both sides are $0$.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 4, sentence after (2.3): "it follows from (2.3) that f′(x̄, d) ≥ ε‖d‖ for some ε > 0 and all d ∈ T_Θ(x̄)"

import Mathlib
import Definitions.Def_SAARate_Sharp_Setting

namespace SAARate.Sharp

open MeasureTheory ProbabilityTheory Filter Topology

theorem dirDeriv_ge_eps_norm {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (Θ : Set (E m)) (hΘ : Convex ℝ Θ) (xbar : E m) (hx : xbar ∈ Θ)
    (h23 : ∀ d ∈ posTangentConeAt Θ xbar, d ≠ 0 → 0 < dirDeriv g xbar d) :
    ∃ ε > 0, ∀ d ∈ posTangentConeAt Θ xbar, ε * ‖d‖ ≤ dirDeriv g xbar d := by sorry

end SAARate.Sharp
