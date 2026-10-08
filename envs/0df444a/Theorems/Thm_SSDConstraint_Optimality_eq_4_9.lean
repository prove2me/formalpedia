-- Prove2me | Theorems.Thm_SSDConstraint_Optimality_eq_4_9
-- name    : SSDConstraint.Optimality.eq_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:32:01.915954+00:00
-- url     : https://prove2.me/theorems/dd6b9af7-f6c4-4dfc-bd1e-e11317e56ee9
-- title:
--   (4.9) — $\int_a^b F_2(X;\eta)\,d\mu(\eta)=-\mathbb E[u(X)]$
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $a,b\in\mathbb R$, $X\in\mathcal L^1(\Omega,\mathcal F,P)$, and let $\mu$ be a finite nonnegative Borel measure on $\mathbb R$ vanishing outside $[a,b]$, with associated function $u(t)=-\int_t^b\mu([\tau,b])\,d\tau$ for $t<b$ and $u(t)=0$ for $t\ge b$. Then
--   $$\int_a^b F_2(X;\eta)\,d\mu(\eta)=-\mathbb E[u(X)].\tag{4.9}$$
--
--   This key identity converts the measure Lagrangian $\Lambda$ of (4.4) into the utility Lagrangian $L$ of (4.1): $\Lambda(X,\mu)=L(X,u)$.
--
--   **Formalization Note** The left integral is over the closed interval $[a,b]$ (atoms at the endpoints count).
-- source:
--   Dentcheva and Ruszczyński, Optimization with stochastic dominance constraints, preprint dated December 27, 2002 (SPEPS; published SIAM J. Optim. 14(2), 2003), p. 10, (4.9) (derived from (4.7)–(4.8), pp. 9–10)

import Mathlib
import Definitions.Def_SSDConstraint_Optimality_Multiplier
open MeasureTheory

namespace SSDConstraint.Optimality

/-- (4.9), p. 10: for every `X ∈ L¹(Ω, ℱ, P)` and every nonnegative measure `μ ∈ rca([a, b])`,
with `u` the utility function of `μ` (p. 9), `∫_a^b F₂(X; η) dμ(η) = −𝔼[u(X)]`. -/
theorem eq_4_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : ℝ) :
    ∀ (X : Ω →₁[P] ℝ) (μ : Measure ℝ), IsFiniteMeasure μ → μ (Set.Icc a b)ᶜ = 0 →
      ∫ η in Set.Icc a b, F2 P X η ∂μ = -∫ ω, uOfMeasure μ b (X ω) ∂P := by sorry

end SSDConstraint.Optimality
