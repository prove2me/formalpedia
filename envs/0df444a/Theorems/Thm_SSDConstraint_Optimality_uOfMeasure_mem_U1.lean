-- Prove2me | Theorems.Thm_SSDConstraint_Optimality_uOfMeasure_mem_U1
-- name    : SSDConstraint.Optimality.uOfMeasure_mem_U1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:31:54.422722+00:00
-- url     : https://prove2.me/theorems/b7e5c8f0-7008-4580-8612-7e9db1fedc3d
-- title:
--   Proof of Theorem 4.2 (pp. 9–10) — the utility function of a nonnegative measure lies in $\mathcal U_1$
-- statement:
--   Let $a,b\in\mathbb R$ and let $\mu$ be a finite nonnegative Borel measure on $\mathbb R$ vanishing outside $[a,b]$. Define
--   $$u(t)=\begin{cases}-\displaystyle\int_t^b\mu([\tau,b])\,d\tau, & t<b,\\[2pt] 0, & t\ge b.\end{cases}$$
--   Then $u\in\mathcal U_1$: $u$ is concave and nondecreasing, $u(t)=0$ for $t\ge b$, and $u(t)=u(a)+c(t-a)$ for all $t\le a$ with some $c\ge0$.
--
--   This is one direction of the correspondence between nonnegative measures in $\mathbf{rca}([a,b])$ and functions in $\mathcal U_1$ that turns the measure multiplier of (4.5)–(4.6) into a utility multiplier.
--
--   **Formalization Note** The slope on $(-\infty,a]$ is $c=\mu([a,b])$, which is $0$ when $\mu=0$; this is why $\mathcal U_1$ is formalized with $c\ge0$ rather than the printed $c>0$.
-- source:
--   Dentcheva and Ruszczyński, Optimization with stochastic dominance constraints, preprint dated December 27, 2002 (SPEPS; published SIAM J. Optim. 14(2), 2003), p. 9 (definition of u and 'Since μ ≥ 0 ... u(·) is nondecreasing and concave'), p. 10 ('a correspondence between nonnegative measures in rca([a,b]) and functions in U_1')

import Mathlib
import Definitions.Def_SSDConstraint_Optimality_Multiplier
open MeasureTheory

namespace SSDConstraint.Optimality

/-- Proof of Theorem 4.2, pp. 9–10: the utility function `u(t) = −∫_t^b μ([τ, b]) dτ` (`t < b`),
`u(t) = 0` (`t ≥ b`) of a nonnegative measure `μ ∈ rca([a, b])` belongs to `𝒰₁`. -/
theorem uOfMeasure_mem_U1 (a b : ℝ) :
    ∀ μ : Measure ℝ, IsFiniteMeasure μ → μ (Set.Icc a b)ᶜ = 0 → uOfMeasure μ b ∈ U1 a b := by sorry

end SSDConstraint.Optimality
