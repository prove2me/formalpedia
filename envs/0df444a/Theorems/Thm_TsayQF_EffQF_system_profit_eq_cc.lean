-- Prove2me | Theorems.Thm_TsayQF_EffQF_system_profit_eq_cc
-- name    : TsayQF.EffQF.system_profit_eq_cc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:25.187584+00:00
-- url     : https://prove2.me/theorems/7ebf3135-2f1c-4e0f-970c-599e83e6cb8c
-- title:
--   §7, p. 1350 (σ_ε = 0) — the QF system earns the centralized expected profit of q(1 + α), so it is maximal when q(1 + α) = Q*_CC
-- statement:
--   Let $p > m > 0$, $u < m$, $s \ge 0$ be the cost data, $c$ any transfer price, and let $\mu$ have law $\nu$ with finite variance and a differentiable, strictly increasing distribution function; with $\sigma_\varepsilon = 0$ demand equals $\mu$. Take a QF contract with $\omega \in [0,1]$, $\alpha \ge -\omega$, and a forecast $q \ge 0$, so that the EM builds $Q = q(1+\alpha)$ and the retailer buys $\mu\perp[q(1-\omega),Q]$. Then the expected system profit equals the central planner's expected profit at the same production:
--   $$\pi_{R,QF}(q, q(1+\alpha)) + \pi_{EM,QF}(q(1+\alpha); q) = \Pi_{CC}(q(1+\alpha)).$$
--   Consequently, if $Q^*_{CC}$ satisfies $F(Q^*_{CC}) = (p+s-m)/(p+s-u)$ and the production level matches it, $q(1+\alpha) = Q^*_{CC}$, then the expected system profit is at least $\Pi_{CC}(Q)$ for every production $Q$: expected system profits are maximized.
--
--   With a perfect demand signal the retailer stocks out only when the EM does, so no product is mispositioned.
--
--   **Formalization Note.** The transfer price cancels between the two firms, so $c$ is unrestricted. The hypotheses $\omega\in[0,1]$ and $\alpha\ge-\omega$ are the contract ranges of §6; they guarantee $q(1-\omega) \le q(1+\alpha)$.
-- source:
--   Tsay, The quantity flexibility contract and supplier-customer incentives, Management Science 45(10) (1999), p. 1350, §7, paragraph before Proposition 6

import Mathlib
import Definitions.Def_TsayQF_EffQF_Model

open MeasureTheory ProbabilityTheory

namespace TsayQF.EffQF

/-- §7, p. 1350: when `σ_ε = 0`, the expected system profit of a QF contract whose EM builds
`q(1 + α)` equals the central planner's expected profit at production `q(1 + α)`; therefore,
when the production level `q(1 + α)` matches `Q*_CC = F^{-1}((p + s − m)/(p + s − u))`, expected
system profit is maximal. -/
theorem system_profit_eq_cc (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hΘ : StrictMono (cdf ν)) (hΘd : Differentiable ℝ (cdf ν)) (hν : MemLp id 2 ν)
    (c α ω : ℝ) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (hα : -ω ≤ α) (q : ℝ) (hq : 0 ≤ q)
    (Qcc : ℝ) (hQcc : cdf ν Qcc = kS D) :
    forecastProfit D ν c α ω q + emProfit D ν c ω q (q * (1 + α)) =
        ccProfit D ν (q * (1 + α)) ∧
      (q * (1 + α) = Qcc → ∀ Q, ccProfit D ν Q ≤
        forecastProfit D ν c α ω q + emProfit D ν c ω q (q * (1 + α))) := by sorry

end TsayQF.EffQF
