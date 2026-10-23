-- Prove2me | Theorems.Thm_PlatformFinance_EndogRate_proposition_8
-- name    : PlatformFinance.EndogRate.proposition_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:39.317154+00:00
-- url     : https://prove2.me/theorems/6e8318f6-086c-497a-8b78-6c85ba76cdf6
-- title:
--   Proposition 8, p. 22 — for δ ≤ δ2 the platform's optimal loan rate is r_f if c ≤ a(1−φ)²/(1+r_f) and below r_f otherwise
-- statement:
--   The platform first sets the interest rate $r$ of its loan; then the supplier and the seller play the platform-financing game at rate $r$. The platform maximizes its equilibrium profit
--   $$\Pi^P_p(r) = \mathbb E\big[\varphi(\tilde a-q^P)q^P + \min\{(1-\varphi)(\tilde a-q^P)q^P,\; w^Pq^P(1+r)\}\big] - w^Pq^P(1+r_f)$$
--   over the rates $-1<r\le \hat r_1(\delta)$ that keep the seller willing to participate.
--
--   Assume $0<\delta<a$, $0\le\varphi<1$, $c>0$, $r_f\ge0$, $(1-\varphi)a>c(1+r_f)$ and low uncertainty, $\delta\le\delta_2$. Fix, for every feasible $r$, a subgame-perfect equilibrium $(w^P(r), q^P(r))$ of the stage game, and let $\Pi^P_p(r)$ be the platform's profit in it. Then:
--
--   1. If $c \le \dfrac{a(1-\varphi)^2}{1+r_f}$, the rate $r^*=r_f$ is feasible and is the unique optimal rate: $\Pi^P_p(r) < \Pi^P_p(r_f)$ for every feasible $r\ne r_f$.
--   2. If $c > \dfrac{a(1-\varphi)^2}{1+r_f}$, an optimal rate exists, and every optimal rate $r^*$ satisfies $r^* < r_f$.
--
--   At low market uncertainty, then, the platform subsidizes the loan below its own capital cost exactly when the product's production cost is high.
--
--   **Formalization Note** The page's "the platform sets $r^*=r_f$" is read as $r_f$ being the unique maximizer, and "$r^*<r_f$" as existence of a maximizer plus every maximizer lying below $r_f$ (without existence the second clause would hold vacuously). The feasible set keeps the page's constraint $r\le\hat r_1(\delta)$ (p. 22) and adds $r>-1$, condition (iii) of p. 36. The page states $\delta\le\delta_2$ while its proof writes $\delta<\delta_2$; the statement follows the page. $\delta<a$ is the reading of p. 8's assumption that the market clearing price is always positive.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 22, Proposition 8 (problem formulated pp. 21–22); proof p. 43

import Mathlib
import Definitions.Def_PlatformFinance_EndogRate_Model

namespace PlatformFinance.EndogRate

/-- Proposition 8 (p. 22): for `δ ≤ δ2`, the platform choosing its loan rate `r` subject to the
seller's participation `r ≤ r̂1(δ)` (and `r > -1`), with the stage-2 game played in a
subgame-perfect equilibrium `σP r` at every feasible `r`, sets `r* = rf` (the unique optimum)
if `c ≤ a(1 - φ)²/(1 + rf)`, and an optimal rate exists and every optimal rate is `< rf` if
`c > a(1 - φ)²/(1 + rf)`. -/
theorem proposition_8 (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hc : 0 < c) (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (hδ2 : δ ≤ delta2 a φ c rf)
    (σP : ℝ → Profile)
    (hP : ∀ r : ℝ, -1 < r → r ≤ rhat1 a δ φ c rf → IsSPEP a δ φ c rf r (σP r)) :
    (c ≤ cbar a φ rf →
      -1 < rf ∧ rf ≤ rhat1 a δ φ c rf ∧
        ∀ r : ℝ, -1 < r → r ≤ rhat1 a δ φ c rf → r ≠ rf →
          platformProfitP a δ φ rf r (σP r) < platformProfitP a δ φ rf rf (σP rf)) ∧
    (cbar a φ rf < c →
      (∃ rs : ℝ, -1 < rs ∧ rs ≤ rhat1 a δ φ c rf ∧
        ∀ r : ℝ, -1 < r → r ≤ rhat1 a δ φ c rf →
          platformProfitP a δ φ rf r (σP r) ≤ platformProfitP a δ φ rf rs (σP rs)) ∧
      ∀ rs : ℝ, -1 < rs → rs ≤ rhat1 a δ φ c rf →
        (∀ r : ℝ, -1 < r → r ≤ rhat1 a δ φ c rf →
          platformProfitP a δ φ rf r (σP r) ≤ platformProfitP a δ φ rf rs (σP rs)) →
        rs < rf) := by sorry

end PlatformFinance.EndogRate
