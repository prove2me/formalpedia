-- Prove2me | Theorems.Thm_SeasonalPricing_MyopicExp_contingent_myopic_revenue_exponential
-- name    : SeasonalPricing.MyopicExp.contingent_myopic_revenue_exponential
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:17:22.753375+00:00
-- url     : https://prove2.me/theorems/e94d88d1-5f97-43c5-a170-cd6f308201c8
-- title:
--   Proposition 3 — with $c = 1$, $\rho = 1$ and unlimited inventory, $\pi^*_{C/N} = (\lambda e^{-1})e^{T/e} = \pi^*_F e^{T/e}$
-- statement:
--   Consider a seller of a seasonal product over the season $[0, H]$ with $H = 1$. Customers arrive as a Poisson process with rate $\lambda > 0$. A premium price $p_1$ applies on $[0, T)$ and a discount price $p_2 \le p_1$ from the discount time $T$ on, where $0 < T \le 1$. Customers are **myopic**: a customer arriving before $T$ buys at $p_1$ if his valuation is at least $p_1$, and otherwise waits and buys at $T$ if his valuation is at least $p_2$; later arrivals buy if their valuation is at least $p_2$. Suppose that
--
--   1. $c = 1$: base valuations are Gamma with mean $\mu = 1$ and coefficient of variation $1$, i.e. exponential with mean one;
--   2. $\rho = e^{-\alpha H} = 1$: valuations do not decline over the season;
--   3. $Q/\lambda \to \infty$: inventory is unlimited.
--
--   Let $\pi^*_{C/N}$ be the maximum over $p_2 \le p_1$ of the expected revenue $p_1\Lambda_I(p_1) + p_2(\Lambda_W(p_1,p_2) + \Lambda_L(p_2))$ of contingent pricing, and $\pi^*_F$ the maximum over $p$ of the fixed-price revenue $p\,\lambda\int_0^1 \bar F(p e^{\alpha t})\,dt$. Then both maxima exist and
--
--   $$
--   \pi^*_{C/N} = (\lambda e^{-1}) \cdot e^{T/e} = \pi^*_F \cdot e^{T/e}.
--   $$
--
--   The proposition quantifies the benefit of a two-price contingent policy over a single price in the simplest nontrivial case: the relative gain is $e^{T/e} - 1$, largest at $T = 1$ where it equals $e^{1/e} - 1$.
--
--   **Formalization Note** "Max" is read as an attained maximum (`IsGreatest`), over all real price pairs $p_2 \le p_1$ and all real prices $p$, as printed. "$Q/\lambda \to \infty$" is read as unlimited inventory: the truncated Poisson means $N(q, \Lambda)$ are replaced by $\Lambda$, which is what the paper's proof computes and what §7.1 calls inventory that is "practically unlimited"; a limit of finite-inventory optima is not stated. The second equality is the product of the two values.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 350, Proposition 3; pp. 358–359, Proof of Proposition 3

import Mathlib
import Definitions.Def_SeasonalPricing_MyopicExp_gammaValuationTail
import Definitions.Def_SeasonalPricing_Shared_LambdaI
import Definitions.Def_SeasonalPricing_MyopicExp_contingentMyopicRevenue

namespace SeasonalPricing.MyopicExp

/-- Proposition 3 (Aviv–Pazgal 2008, p. 350). Suppose `c = 1`, `ρ = 1` and `Q/λ → ∞` (read as
unlimited inventory), with mean base valuation `μ = 1` and season length `H = 1`, arrival rate
`λ > 0` and discount time `0 < T ≤ 1`. Then the optimal expected revenue of contingent pricing
with myopic customers is `π*_{C/N} = (λe^{−1}) · e^{T/e}`, the optimal fixed-price revenue is
`π*_F = λe^{−1}`, so that `π*_{C/N} = π*_F · e^{T/e}`. Both optima are attained maxima over all
price pairs `p₂ ≤ p₁`, respectively all single prices `p`. -/
theorem contingent_myopic_revenue_exponential (lam α T : ℝ) (hlam : 0 < lam) (hT0 : 0 < T)
    (hT1 : T ≤ 1) (hα : 0 ≤ α) (hρ : decayRatio α 1 = 1) :
    IsGreatest {r : ℝ | ∃ p1 p2 : ℝ, p2 ≤ p1 ∧
        r = contingentMyopicRevenue lam α T 1 (gammaValuationTail 1 1) p1 p2}
      (lam * Real.exp (-1) * Real.exp (T / Real.exp 1)) ∧
    IsGreatest {r : ℝ | ∃ p : ℝ, r = fixedPriceRevenue lam α 1 (gammaValuationTail 1 1) p}
      (lam * Real.exp (-1)) := by sorry

end SeasonalPricing.MyopicExp
