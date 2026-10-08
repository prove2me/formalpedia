-- Prove2me | Theorems.Thm_SAARate_Sharp_prop_2_2_eq_2_5
-- name    : SAARate.Sharp.prop_2_2_eq_2_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:07:23.167847+00:00
-- url     : https://prove2.me/theorems/64cebd9c-7954-4483-8903-d1b08c1ea222
-- title:
--   Proposition 2.2, (2.5), p. 5 — f′(x, d) = E_P h′_ω(x, d), with h′_ω(x, d) integrable
-- statement:
--   Let $P$ be a probability measure on $(\Omega,\mathcal F)$ and $h:\mathbb R^m\times\Omega\to\mathbb R$. Suppose that
--
--   1. for every $\omega\in\Omega$ the function $h(\cdot,\omega)$ is convex;
--   2. the expected value function $f(x)=\mathbb E_P h(x,\omega)$ is well defined and finite valued.
--
--   Then for all $x,d\in\mathbb R^m$ the function $\omega\mapsto h'_\omega(x,d)$ is $P$-integrable and
--   $$
--   f'(x,d)=\mathbb E_P\{h'_\omega(x,d)\}, \tag{2.5}
--   $$
--   where $h'_\omega(x,d)$ is the directional derivative of $h(\cdot,\omega)$ at $x$ in the direction $d$ and $f'(x,d)$ that of $f$.
--
--   Exchanging the directional derivative with the expectation is what lets the strong law of large numbers act on directional derivatives in (2.6).
--
--   **Formalization Note.** Assumption 2 is encoded as integrability of $h(x,\cdot)$ for every $x$ (which includes its measurability). The integrability of $h'_\cdot(x,d)$ is part of the conclusion: it is the page's "the right hand side of (2.5) is well defined" (proof of Proposition 2.2, p. 5), and without it the Bochner integral of a non-integrable function would be $0$.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 5, Proposition 2.2, (2.5)

import Mathlib
import Definitions.Def_SAARate_Sharp_Setting

namespace SAARate.Sharp

open MeasureTheory ProbabilityTheory Filter Topology

theorem prop_2_2_eq_2_5 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (hint : ∀ x, Integrable (h x) P) :
    ∀ x d : E m, Integrable (fun ω => dirDeriv (fun y => h y ω) x d) P ∧
      dirDeriv (expectedObj P h) x d = ∫ ω, dirDeriv (fun y => h y ω) x d ∂P := by sorry

end SAARate.Sharp
