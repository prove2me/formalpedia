-- Prove2me | Theorems.Thm_SSDConstraint_Optimality_expectation_finite
-- name    : SSDConstraint.Optimality.expectation_finite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:08:58.657967+00:00
-- url     : https://prove2.me/theorems/5832b714-c5da-4c36-808d-6ae586023d98
-- title:
--   p. 8 after (4.1) — $\mathbb E[u(X)]$ exists and is finite for $u\in\mathcal U_1$, $X\in\mathcal L^1$
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $a,b\in\mathbb R$, and let $\mathcal U_1$ be the class of concave nondecreasing $u:\mathbb R\to\mathbb R$ with $u(t)=0$ for $t\ge b$ and $u(t)=u(a)+c(t-a)$ for $t\le a$, for some $c\ge0$. Then for every $u\in\mathcal U_1$ and every $X\in\mathcal L^1(\Omega,\mathcal F,P)$,
--   $$\mathbb E\,|u(X)|<\infty,$$
--   i.e. the expected value $\mathbb E[u(X)]$ exists and is finite.
--
--   This is what makes the Lagrangian $L(X,u)=f(X)+\mathbb E[u(X)]-\mathbb E[u(Y)]$ of (4.1) well defined.
--
--   **Formalization Note** "Exists and is finite" is stated as integrability of $u\circ X$; $\mathcal U_1$ uses $c\ge0$ (the page prints $c>0$, see the definition item).
-- source:
--   Dentcheva and Ruszczyński, Optimization with stochastic dominance constraints, preprint dated December 27, 2002 (SPEPS; published SIAM J. Optim. 14(2), 2003), p. 8, sentence after (4.1)

import Mathlib
import Definitions.Def_SSDConstraint_Optimality_Problem
open MeasureTheory

namespace SSDConstraint.Optimality

/-- p. 8, after (4.1): for every `u ∈ 𝒰₁` and every `X ∈ L¹(Ω, ℱ, P)` the expected value
`𝔼[u(X)]` exists and is finite, i.e. `u ∘ X` is integrable. -/
theorem expectation_finite {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (a b : ℝ) :
    ∀ u ∈ U1 a b, ∀ X : Ω →₁[P] ℝ, Integrable (fun ω => u (X ω)) P := by sorry

end SSDConstraint.Optimality
