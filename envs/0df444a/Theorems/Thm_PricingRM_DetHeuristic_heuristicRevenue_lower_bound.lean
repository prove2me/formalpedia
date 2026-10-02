-- Prove2me | Theorems.Thm_PricingRM_DetHeuristic_heuristicRevenue_lower_bound
-- name    : PricingRM.DetHeuristic.heuristicRevenue_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:35:46.665495+00:00
-- url     : https://prove2.me/theorems/712cc73b-59bc-4e37-b94b-c82c824070f7
-- title:
--   Appendix, Proof of Proposition 8 — revenue of fixed prices bounded below by expected cumulative overflow
-- statement:
--   In the $N$-period model, fix prices $p^{\det}_1, \dots, p^{\det}_N \ge 0$ with $E[D_n(p^{\det}_n)] > 0$ for every $n$, let the demands $D_n = D_n(p^{\det}_n)$ be independent, and let $\mathscr{D}_n = \sum_{i=1}^n D_i$ ($\mathscr{D}_0 = 0$). The expected revenue $V_1(p^{\det}, C_0)$ of charging these prices satisfies
--   $$
--   V_1(p^{\det}, C_0) = \sum_{n=1}^N p_n^{\det} E[D_n]\left(1 - \frac{E\big[\big(D_n - (C_0 - \mathscr{D}_{n-1})^+\big)^+\big]}{E[D_n]}\right) \ge \sum_{n=1}^N p_n^{\det} E[D_n]\left(1 - \frac{E\big[(\mathscr{D}_n - C_0)^+\big]}{E[D_n]}\right).
--   $$
--
--   The lost sales of period $n$ are at most the overflow of the cumulative demand over the capacity. Combined with Gallego's bound this gives the lower bound on the heuristic's revenue in Proposition 8.
--
--   **Formalization Note** $V_1(p^{\det}, C_0)$ is `heuristicRevenue`, defined by the first expression of the paper's display with the joint law of the demands the product measure; the first equality therefore uses only the definition and linearity of expectation. The statement holds for any nonnegative prices with positive mean demands; the paper applies it to the optimal deterministic prices.
-- source:
--   Bitran and Caldentey, An Overview of Pricing Models for Revenue Management, MSOM 5(3) 2003, p. 227, Appendix, Proof of Proposition 8 (unnumbered display)

import Mathlib
import Definitions.Def_PricingRM_DetHeuristic_PricingModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PricingRM.DetHeuristic

/-- Bitran–Caldentey (2003), Appendix, Proof of Proposition 8, p. 227: for fixed prices
`pdet ≥ 0` with `E[D_n(pdet_n)] > 0` for every period, the expected revenue of charging them
satisfies
`V_1(pdet, C₀) = ∑_n pdet_n E[D_n] (1 - E[(D_n - (C₀ - 𝒟_{n-1})^+)^+] / E[D_n])
  ≥ ∑_n pdet_n E[D_n] (1 - E[(𝒟_n - C₀)^+] / E[D_n])`,
with `D_n = D_n(pdet_n)` independent across periods and `𝒟_n` the cumulative demand. -/
theorem heuristicRevenue_lower_bound {N : ℕ} (M : PricingModel N) (C₀ : ℝ) (pdet : Fin N → ℝ)
    (hp : ∀ n, 0 ≤ pdet n) (hmean : ∀ n, 0 < meanDemand M n (pdet n)) :
    heuristicRevenue M C₀ pdet =
        ∑ n, pdet n * meanDemand M n (pdet n) *
          (1 - (∫ x, max (x n - max (C₀ - cumDemandBefore x n) 0) 0 ∂(heuristicLaw M pdet)) /
            meanDemand M n (pdet n)) ∧
      ∑ n, pdet n * meanDemand M n (pdet n) *
          (1 - (∫ x, max (x n - max (C₀ - cumDemandBefore x n) 0) 0 ∂(heuristicLaw M pdet)) /
            meanDemand M n (pdet n)) ≥
        ∑ n, pdet n * meanDemand M n (pdet n) *
          (1 - (∫ x, max (cumDemand x n - C₀) 0 ∂(heuristicLaw M pdet)) /
            meanDemand M n (pdet n)) := by sorry

end PricingRM.DetHeuristic
