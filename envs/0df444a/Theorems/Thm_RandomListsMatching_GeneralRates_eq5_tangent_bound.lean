-- Prove2me | Theorems.Thm_RandomListsMatching_GeneralRates_eq5_tangent_bound
-- name    : RandomListsMatching.GeneralRates.eq5_tangent_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:28.158046+00:00
-- url     : https://prove2.me/theorems/eca5892b-f775-4a10-9d37-a579ce57abb3
-- title:
--   (5), p. 15, analytic part — h(y, 0) − h(y, x) ≤ −x ∂ₓh(y, 0) ≤ e⁻¹x for 0 ≤ x ≤ y ≤ 1
-- statement:
--   Let $h$ be the function of Claim 2,
--   $$
--   h(y,x)=\begin{cases}\dfrac{y}{y-x}\,\bigl(e^{-x}-e^{-y}\bigr), & x\neq y,\\[4pt] y\,e^{-y}, & x=y,\end{cases}\qquad g(y,x)=h(y,0)-h(y,x).
--   $$
--   and write $\partial_2 h(y, 0)$ for the derivative of $t \mapsto h(y, t)$ at $t = 0$. For $0 \le x \le y \le 1$,
--   $$
--   h(y, 0) - h(y, x) \;\le\; -x\,\partial_2 h(y, 0) \;\le\; e^{-1}\,x .
--   $$
--
--   This is the analytic content of inequality (5) of Jaillet and Lu, applied there with $y = f_{a_1}$ and $x = m_{a_1,a}$: the first inequality is the tangent-line bound for the convex function $h(y,\cdot)$, the second a bound on its slope at $0$. Since $h(y,0) - h(y,x) = g(y,x)$, it gives $g(y, x) \le x/e$.
--
--   **Formalization Note** The page writes $\partial h/\partial y(f_{a_1}, 0)$; the derivative meant is the one in the second argument (the sentence before (5) speaks of "the convexity of $h$ in the second argument"), and that is what is stated. The probabilistic left-hand side $\mathbb P(E_{a_1,a})$ of (5) comes from Claim 2, which is an asymptotic ("$\approx$") statement and is not part of this mission. At $y = 0$ (hence $x = 0$) both sides vanish.
-- source:
--   Jaillet & Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (rev. June 2013), p. 15, inequality (5) (analytic part; the left equality P(E_{a1,a}) = … is Claim 2, not formalized)

import Mathlib
import Definitions.Def_RandomListsMatching_GeneralRates_Setting

namespace RandomListsMatching.GeneralRates

theorem eq5_tangent_bound (y x : ℝ) (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    h y 0 - h y x ≤ -x * deriv (fun t => h y t) 0 ∧
      -x * deriv (fun t => h y t) 0 ≤ Real.exp (-1) * x := by sorry

end RandomListsMatching.GeneralRates
