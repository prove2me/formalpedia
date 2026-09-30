-- Prove2me | Theorems.Thm_PricingRM_DetHeuristic_optValue_le_detValue
-- name    : PricingRM.DetHeuristic.optValue_le_detValue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:35:20.070046+00:00
-- url     : https://prove2.me/theorems/58774259-bafb-4971-81ca-d6fad74d3e0b
-- title:
--   Proposition 8 (first assertion) — $V_1(C_0) \le V_1^{\det}(C_0)$
-- statement:
--   In the $N$-period model, suppose that for every period $n$ the revenue rate $p \mapsto p\,E[D_n(p)]$ is concave on $[0,\infty)$ and the mean demand $p \mapsto E[D_n(p)]$ is convex on $[0,\infty)$ (the deterministic problem (32)–(33) has a concave objective and a convex feasible region), and that there is a price $p^\infty \ge 0$ with
--   $$
--   \sum_{n=1}^N E[D_n(p^\infty)] < C_0 .
--   $$
--   Then the optimal expected revenue of the stochastic problem is bounded by the optimal value of the deterministic problem:
--   $$
--   V_1(C_0) \le V_1^{\det}(C_0).
--   $$
--
--   The deterministic (fluid) problem is thus an upper bound on what any pricing policy can earn in expectation. It is the benchmark against which Proposition 8 measures the deterministic-price heuristic.
--
--   **Formalization Note** $V_1(C_0)$ is the Bellman value `optValue` in $[0,\infty]$, cast to `EReal`; $V_1^{\det}(C_0)$ is the `EReal` supremum `detValue`, so the statement also covers an unbounded deterministic problem. The paper's "concave objective and convex feasible region" is read as the two per-period hypotheses stated above.
-- source:
--   Bitran and Caldentey, An Overview of Pricing Models for Revenue Management, MSOM 5(3) 2003, p. 221, Proposition 8 (first assertion); proof in the Appendix, pp. 226–227

import Mathlib
import Definitions.Def_PricingRM_DetHeuristic_PricingModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PricingRM.DetHeuristic

/-- Bitran–Caldentey (2003), Proposition 8, first assertion, p. 221: if the deterministic
problem (32)–(33) has a concave objective and a convex feasible region, and some price
`p^∞ ≥ 0` has `∑_n E[D_n(p^∞)] < C₀`, then the optimal expected revenue is bounded by the
deterministic value: `V_1(C₀) ≤ V_1^det(C₀)`. -/
theorem optValue_le_detValue {N : ℕ} (M : PricingModel N)
    (hconc : ∀ n, ConcaveOn ℝ (Set.Ici 0) (fun p => p * meanDemand M n p))
    (hconv : ∀ n, ConvexOn ℝ (Set.Ici 0) (meanDemand M n))
    (C₀ : ℝ) (hslater : ∃ pinf : ℝ, 0 ≤ pinf ∧ ∑ n, meanDemand M n pinf < C₀) :
    ((optValue M C₀ : ℝ≥0∞) : EReal) ≤ detValue M C₀ := by sorry

end PricingRM.DetHeuristic
