-- Prove2me | Theorems.Thm_PersonalizedRM_RevenueGap_revenue_lipschitz
-- name    : PersonalizedRM.RevenueGap.revenue_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:01.129336+00:00
-- url     : https://prove2.me/theorems/f33187e9-3133-4ffe-b55f-343b67501c6b
-- title:
--   Proof of Proposition 1, pp. 17–18 — |f_z(S, p; θ) − f_z(S, p; θ′)| ≤ (J/4)√(J(d + 1))‖θ − θ′‖₂
-- statement:
--   Let $z \in \mathbb R^d$ with $\|z\|_\infty \le 1$, let $S \subseteq [J]$ and let $p \in [0,1]^J$. For any two parameters $\theta, \theta'$,
--
--   $$|f_z(S, p; \theta) - f_z(S, p; \theta')| \ \le\ \frac J4 \sqrt{J(d+1)}\; \|\theta - \theta'\|_2 .$$
--
--   The expected revenue is thus Lipschitz in the parameter, uniformly in the feature vector, the assortment and the prices. The page derives it from the bound $1/4$ on every partial derivative of the MNL purchase probabilities. Combined with Theorem 1 it gives the uniform revenue forecast bound of Proposition 1.
--
--   **Formalization Note.** Prices are only required to lie in $[0,1]$, which contains the price box $[p_{\min}, 1]$; the page uses only $p_j \le p_{\max} = 1$.
-- source:
--   Chen, Owen, Pixton & Simchi-Levi, A statistical learning approach to personalization in revenue management, author manuscript (SSRN 2579462; Management Science 2021), pp. 17–18, proof of Proposition 1

import Mathlib
import Definitions.Def_PersonalizedRM_RevenueGap_Model

open MeasureTheory ProbabilityTheory

namespace PersonalizedRM.RevenueGap

/-- Proof of Proposition 1, pp. 17–18: for a bounded feature vector and prices in `[0, 1]`, the
expected revenue is Lipschitz in the parameter,
`|f_z(S, p; θ) − f_z(S, p; θ')| ≤ (J/4) √(J(d + 1)) ‖θ − θ'‖₂`. -/
theorem revenue_lipschitz {J d : ℕ} (θ θ' : Param J d) (z : Fin d → ℝ) (hz : ∀ k, |z k| ≤ 1)
    (S : Finset (Fin J)) (p : Fin J → ℝ) (hp : p ∈ priceBox J 0) :
    |revenue θ z S p - revenue θ' z S p| ≤
      (J : ℝ) / 4 * Real.sqrt ((J : ℝ) * ((d : ℝ) + 1)) * ‖θ - θ'‖ := by sorry

end PersonalizedRM.RevenueGap
