-- Prove2me | Theorems.Thm_SSDConstraint_Optimality_U1_eq_uOfMeasure_unique
-- name    : SSDConstraint.Optimality.U1_eq_uOfMeasure_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:32:14.674823+00:00
-- url     : https://prove2.me/theorems/81aaca79-dab3-489e-87ee-0fe99efecdbe
-- title:
--   Proof of Theorem 4.2 (p. 10) — every $u\in\mathcal U_1$ comes from a unique nonnegative measure on $[a,b]$
-- statement:
--   Let $a,b\in\mathbb R$ and $u\in\mathcal U_1$. Then there is exactly one finite nonnegative Borel measure $\mu$ on $\mathbb R$ vanishing outside $[a,b]$ such that
--   $$u(t)=\begin{cases}-\displaystyle\int_t^b\mu([\tau,b])\,d\tau, & t<b,\\[2pt] 0, & t\ge b,\end{cases}\qquad t\in\mathbb R.$$
--
--   Together with the fact that the function of every such measure lies in $\mathcal U_1$, this is the bijection between nonnegative measures in $\mathbf{rca}([a,b])$ and $\mathcal U_1$, which makes (4.9) valid for every $u\in\mathcal U_1$.
--
--   **Formalization Note** The page identifies $\mu$ through $\mu([t,b])=u'_-(t)$ (the left derivative); the statement records existence and uniqueness of the representing measure. $\mathcal U_1$ uses $c\ge0$ (the page prints $c>0$, see the definition item).
-- source:
--   Dentcheva and Ruszczyński, Optimization with stochastic dominance constraints, preprint dated December 27, 2002 (SPEPS; published SIAM J. Optim. 14(2), 2003), p. 10, proof of Theorem 4.2, 'Let us now prove the converse ... the correspondence ... is a bijection'

import Mathlib
import Definitions.Def_SSDConstraint_Optimality_Multiplier
open MeasureTheory

namespace SSDConstraint.Optimality

/-- Proof of Theorem 4.2, p. 10: every `u ∈ 𝒰₁` is the utility function of exactly one nonnegative
measure `μ ∈ rca([a, b])` (a finite Borel measure on `ℝ` vanishing off `[a, b]`). -/
theorem U1_eq_uOfMeasure_unique (a b : ℝ) :
    ∀ u ∈ U1 a b, ∃! μ : Measure ℝ, IsFiniteMeasure μ ∧ μ (Set.Icc a b)ᶜ = 0 ∧
      u = uOfMeasure μ b := by sorry

end SSDConstraint.Optimality
