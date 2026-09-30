-- Prove2me | Theorems.Thm_PricingRM_DetHeuristic_det_price_heuristic_ratio_bound
-- name    : PricingRM.DetHeuristic.det_price_heuristic_ratio_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:36:19.32526+00:00
-- url     : https://prove2.me/theorems/21cce9be-ce6a-42db-bc78-c0a6b66c0579
-- title:
--   Proposition 8, eq. (35) — performance guarantee of the deterministic price heuristic
-- statement:
--   Consider the $N$-period pricing model ($N \ge 1$) with initial inventory $C_0$. Assume:
--
--   1. for every period $n$, the revenue rate $p \mapsto p\,E[D_n(p)]$ is concave on $[0,\infty)$, and the mean demand $p \mapsto E[D_n(p)]$ is convex on $[0,\infty)$ (the deterministic problem (32)–(33) has a concave objective and a convex feasible region);
--   2. there is a price $p^\infty \ge 0$ with $\sum_{n=1}^N E[D_n(p^\infty)] < C_0$;
--   3. $p^{\det} = (p^{\det}_1, \dots, p^{\det}_N)$ is an optimal solution of (32)–(33), so $V_1^{\det}(C_0) = \sum_n p^{\det}_n E[D_n(p^{\det}_n)]$;
--   4. each $D_n(p^{\det}_n)$ has finite variance and positive mean, and $V_1^{\det}(C_0) > 0$.
--
--   Let $V_1(C_0)$ be the optimal expected revenue, $V_1(p^{\det}, C_0)$ the expected revenue of charging $p^{\det}_n$ in period $n$ regardless of sales (with independent period demands), and $\eta^{\det}_n(C_0)$ the quantity (34) built from the mean and variance of the cumulative demand $\mathscr{D}_n^{\det} = \sum_{i=1}^n D_i(p_i^{\det})$. Then
--   $$
--   1 \ge \frac{V_1(p^{\det}, C_0)}{V_1(C_0)} \ge \frac{1}{V_1^{\det}(C_0)} \sum_{n=1}^N p_n^{\det} E[D_n(p_n^{\det})]\left(1 - \frac{\eta_n^{\det}(C_0)}{E[D_n(p_n^{\det})]}\right) \ge 1 - \max_n \frac{\eta_n^{\det}(C_0)}{E[D_n(p_n^{\det})]}.
--   $$
--
--   The result is a distribution-free guarantee: fixing the prices that solve the deterministic problem loses a fraction of the optimal expected revenue that depends only on the first two moments of the cumulative demand.
--
--   **Formalization Note** $V_1(C_0)$ is the Bellman value `optValue` (computed in $[0,\infty]$ and converted to a real number for the ratio), $V_1(p^{\det}, C_0)$ is `heuristicRevenue` under the product law of the demands, and $\eta_n^{\det}(C_0)$ is `eta` evaluated at $p^{\det}$, exactly expression (34). The paper's "concave objective and convex feasible region" is read as hypothesis 1. Existence of the optimal deterministic solution, finite variances, positive means and $V_1^{\det}(C_0) > 0$ are made explicit because the paper names $p^{\det}$, takes variances and divides by these quantities without comment. The maximum over $n$ is `Finset.sup'` over the nonempty index set.
-- source:
--   Bitran and Caldentey, An Overview of Pricing Models for Revenue Management, MSOM 5(3) 2003, p. 221, Proposition 8, eq. (35) (definitions (32)–(34) on the same page); proof in the Appendix, pp. 226–227

import Mathlib
import Definitions.Def_PricingRM_DetHeuristic_PricingModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PricingRM.DetHeuristic

/-- Bitran–Caldentey (2003), Proposition 8, eq. (35), p. 221: under the hypotheses of the
proposition, with `pdet` an optimal solution of (32)–(33),
`1 ≥ V_1(pdet, C₀) / V_1(C₀)
   ≥ (1 / V_1^det(C₀)) ∑_n pdet_n E[D_n(pdet_n)] (1 - η_n(C₀) / E[D_n(pdet_n)])
   ≥ 1 - max_n η_n(C₀) / E[D_n(pdet_n)]`. -/
theorem det_price_heuristic_ratio_bound {N : ℕ} (M : PricingModel N) (hN : 0 < N)
    (hconc : ∀ n, ConcaveOn ℝ (Set.Ici 0) (fun p => p * meanDemand M n p))
    (hconv : ∀ n, ConvexOn ℝ (Set.Ici 0) (meanDemand M n))
    (C₀ : ℝ) (hslater : ∃ pinf : ℝ, 0 ≤ pinf ∧ ∑ n, meanDemand M n pinf < C₀)
    (pdet : Fin N → ℝ) (hopt : IsDetOptimal M C₀ pdet)
    (hL2 : ∀ n, MemLp (fun x : ℝ => x) 2 (M.μ n (pdet n)))
    (hmean : ∀ n, 0 < meanDemand M n (pdet n))
    (hVdet : 0 < detObjective M pdet) :
    1 ≥ heuristicRevenue M C₀ pdet / (optValue M C₀).toReal ∧
      heuristicRevenue M C₀ pdet / (optValue M C₀).toReal ≥
        (1 / detObjective M pdet) *
          ∑ n, pdet n * meanDemand M n (pdet n) *
            (1 - eta M C₀ pdet n / meanDemand M n (pdet n)) ∧
      (1 / detObjective M pdet) *
          ∑ n, pdet n * meanDemand M n (pdet n) *
            (1 - eta M C₀ pdet n / meanDemand M n (pdet n)) ≥
        1 - Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
          (fun n => eta M C₀ pdet n / meanDemand M n (pdet n)) := by sorry

end PricingRM.DetHeuristic
