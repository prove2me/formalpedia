-- Prove2me | Theorems.Thm_SeasonalPricing_MyopicDet_optimal_prices_and_discount_time
-- name    : SeasonalPricing.MyopicDet.optimal_prices_and_discount_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:03:04.355545+00:00
-- url     : https://prove2.me/theorems/028005d5-8ebe-4c0f-9a9c-40f81a41843a
-- title:
--   Proposition 4 — optimal prices and discount time with myopic customers and identical declining valuations
-- statement:
--   A seller with unlimited inventory sells a seasonal product over the season $[0, 1]$. Customers arrive as a Poisson process with rate $\lambda > 0$; every customer has base valuation $1$ (coefficient of variation $c = 0$), and a customer's valuation at time $t$ is $\rho^t$ for a fixed $0 < \rho < 1$. The seller posts a premium price $p_1$ until a discount time $T \in [0, 1]$ and a discount price $p_2 \le p_1$ afterwards. Customers are myopic: one arriving at time $t < T$ buys at once iff $\rho^t \ge p_1$, otherwise waits and buys at $T$ iff $\rho^T \ge p_2$; one arriving after $T$ buys iff the current valuation is at least $p_2$. Let $R_\rho(p_1, p_2; T)$ be the expected revenue, and
--
--   $$
--   G(p_1, p_2) = (p_1 - p_2)\cdot\frac{\ln p_1}{\ln\rho} + p_2\cdot\frac{\ln p_2}{\ln\rho}.
--   $$
--
--   1. The problem $\max_{\rho \le p_2 \le p_1 \le 1} G(p_1, p_2)$ has a maximum $M$, and
--   $$
--   \pi^*_{C/N} = \lambda M = \max\big\{R_\rho(p_1, p_2; T) : 0 < p_2 \le p_1,\ 0 \le T \le 1\big\};
--   $$
--   moreover, for every maximizer $(p_1^*, p_2^*)$ of $G$ on the region and every $T$ with $p_2^* \le \rho^T \le p_1^*$, $R_\rho(p_1^*, p_2^*; T) = \pi^*_{C/N}$.
--   2. If $\rho \le e^{-2+e^{-1}}$, then the maximizer is unique, $p_1^* = e^{-1+e^{-1}}$, $p_2^* = p_1^*/e$, the optimal revenue is $\pi^*_{C/N} = -\lambda e^{-1+e^{-1}}/\ln\rho$, and every $T$ with
--   $$
--   \rho^T \in \big[e^{-2+e^{-1}},\, e^{-1+e^{-1}}\big]
--   $$
--   gives $R_\rho(p_1^*, p_2^*; T) = \pi^*_{C/N}$.
--
--   The result says that with identical, declining valuations the seller segments customers by arrival time alone: early arrivals pay the premium price, later ones the discount, and the discount time can be placed anywhere in a whole interval without loss.
--
--   **Formalization Note** The paper's "Q/λ → ∞" is read as unlimited inventory. Prices in the revenue maximization range over all $0 < p_2 \le p_1$ and discount times over $[0, 1]$; the restriction to $\rho \le p_2 \le p_1 \le 1$ is part of the conclusion, not an assumption. "Setting $T$ to any value within the range $p_2^* \le \rho^T \le p_1^*$" is read as: every such $T$ is optimal (not: only such $T$). "If one could, it would be optimal to select $T$ so that $\rho^T \in [e^{-2+e^{-1}}, e^{-1+e^{-1}}]$" is read the same way, at the explicit prices. Such $T$ automatically lie in $[0, 1]$. Uniqueness in part 2 is the reading of "the prices $p_1^*$ and $p_2^*$". The decimal approximations $0.196$ and $0.532$ are not stated.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 351, Proposition 4

import Mathlib
import Definitions.Def_SeasonalPricing_MyopicDet_myopicRevenue
import Definitions.Def_SeasonalPricing_MyopicDet_reducedObjective

namespace SeasonalPricing.MyopicDet

/-- Proposition 4 (Aviv–Pazgal 2008, p. 351). Myopic customers, identical base valuations
`V = 1` (`c = 0`), `0 < ρ < 1` (`α = −ln ρ`, `H = 1`), unlimited inventory (`Q/λ → ∞`),
and the discount time `T ∈ [0, 1]` chosen by the seller together with the prices.

(a) The problem `max_{ρ ≤ p₂ ≤ p₁ ≤ 1} G(p₁, p₂)`, `G = (p₁ − p₂) ln(p₁)/ln(ρ) + p₂ ln(p₂)/ln(ρ)`,
has a maximum `M`; `λM` is the maximal expected revenue over all prices `0 < p₂ ≤ p₁` and
discount times `T ∈ [0, 1]`; and every maximizer `(p₁*, p₂*)` of `G` together with every `T`
with `p₂* ≤ ρ^T ≤ p₁*` attains it.

(b) If `ρ ≤ e^{−2+e^{−1}}`, the maximizer is unique, `p₁* = e^{−1+e^{−1}}`, `p₂* = p₁*/e`, the
optimal revenue is `π*_{C/N} = −λ e^{−1+e^{−1}}/ln(ρ)`, and every `T` with
`ρ^T ∈ [e^{−2+e^{−1}}, e^{−1+e^{−1}}]` attains it at these prices. -/
theorem optimal_prices_and_discount_time (lam ρ : ℝ) (hlam : 0 < lam) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) :
    (∃ M : ℝ,
      IsGreatest {g : ℝ | ∃ p1 p2 : ℝ, ρ ≤ p2 ∧ p2 ≤ p1 ∧ p1 ≤ 1 ∧
          g = reducedObjective ρ p1 p2} M ∧
      IsGreatest {r : ℝ | ∃ p1 p2 T : ℝ, 0 < p2 ∧ p2 ≤ p1 ∧ 0 ≤ T ∧ T ≤ 1 ∧
          r = detRevenue lam ρ p1 p2 T} (lam * M) ∧
      ∀ p1 p2 : ℝ, ρ ≤ p2 → p2 ≤ p1 → p1 ≤ 1 → reducedObjective ρ p1 p2 = M →
        ∀ T : ℝ, p2 ≤ ρ ^ T → ρ ^ T ≤ p1 → detRevenue lam ρ p1 p2 T = lam * M) ∧
    (ρ ≤ Real.exp (-2 + Real.exp (-1)) →
      IsGreatest {g : ℝ | ∃ p1 p2 : ℝ, ρ ≤ p2 ∧ p2 ≤ p1 ∧ p1 ≤ 1 ∧
          g = reducedObjective ρ p1 p2} (-Real.exp (-1 + Real.exp (-1)) / Real.log ρ) ∧
      (∀ p1 p2 : ℝ, ρ ≤ p2 → p2 ≤ p1 → p1 ≤ 1 →
        reducedObjective ρ p1 p2 = -Real.exp (-1 + Real.exp (-1)) / Real.log ρ →
          p1 = Real.exp (-1 + Real.exp (-1)) ∧
            p2 = Real.exp (-1 + Real.exp (-1)) / Real.exp 1) ∧
      IsGreatest {r : ℝ | ∃ p1 p2 T : ℝ, 0 < p2 ∧ p2 ≤ p1 ∧ 0 ≤ T ∧ T ≤ 1 ∧
          r = detRevenue lam ρ p1 p2 T} (-lam * Real.exp (-1 + Real.exp (-1)) / Real.log ρ) ∧
      ∀ T : ℝ, Real.exp (-2 + Real.exp (-1)) ≤ ρ ^ T → ρ ^ T ≤ Real.exp (-1 + Real.exp (-1)) →
        detRevenue lam ρ (Real.exp (-1 + Real.exp (-1)))
            (Real.exp (-1 + Real.exp (-1)) / Real.exp 1) T =
          -lam * Real.exp (-1 + Real.exp (-1)) / Real.log ρ) := by sorry

end SeasonalPricing.MyopicDet
