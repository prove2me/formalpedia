-- Prove2me | Theorems.Thm_SSDConstraint_Optimality_expectedUtility_ge_of_dominance
-- name    : SSDConstraint.Optimality.expectedUtility_ge_of_dominance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:09:11.728034+00:00
-- url     : https://prove2.me/theorems/ec24e124-924a-440b-8742-23bd9a5e85de
-- title:
--   §5 (p. 11) — the dominance constraint (3.2) implies $\mathbb E[u(X)]\ge\mathbb E[u(Y)]$ for $u\in\mathcal U_1$
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $Y\in\mathcal L^1$, $a,b\in\mathbb R$, and $X\in\mathcal L^1$ such that
--   $$\mathbb E[(\eta-X)_+]\le\mathbb E[(\eta-Y)_+]\qquad\text{for all }\eta\in[a,b].\tag{3.2}$$
--   Then for every $u\in\mathcal U_1$,
--   $$\mathbb E[u(X)]\ge\mathbb E[u(Y)].$$
--
--   This is weak duality for the Lagrangian relaxation (5.1): every feasible point of (3.1)–(3.3) has $L(X,u)\ge f(X)$, and it is the step behind the sufficiency half of Theorem 4.2.
--
--   **Formalization Note** $Y$ and $[a,b]$ are taken from problem data whose other fields do not enter. $\mathcal U_1$ uses $c\ge0$ (the page prints $c>0$, see the definition item).
-- source:
--   Dentcheva and Ruszczyński, Optimization with stochastic dominance constraints, preprint dated December 27, 2002 (SPEPS; published SIAM J. Optim. 14(2), 2003), p. 11, §5, after the definition of D(u): 'the dominance relation (3.2) implies that E[u(X)] ≥ E[u(Y)]'

import Mathlib
import Definitions.Def_SSDConstraint_Optimality_Problem
open MeasureTheory

namespace SSDConstraint.Optimality

/-- §5, p. 11: the dominance relation (3.2) on `[a, b]` implies `𝔼[u(X)] ≥ 𝔼[u(Y)]` for every
`u ∈ 𝒰₁`. -/
theorem expectedUtility_ge_of_dominance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (pr : Problem Ω P) :
    ∀ u ∈ U1 pr.a pr.b, ∀ X : Ω →₁[P] ℝ,
      (∀ η ∈ Set.Icc pr.a pr.b, ∫ ω, max (η - X ω) 0 ∂P ≤ ∫ ω, max (η - pr.Y ω) 0 ∂P) →
      ∫ ω, u (pr.Y ω) ∂P ≤ ∫ ω, u (X ω) ∂P := by sorry

end SSDConstraint.Optimality
