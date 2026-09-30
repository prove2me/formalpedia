-- Prove2me | Theorems.Thm_PricingRM_DetHeuristic_time_homogeneous_ratio_bound
-- name    : PricingRM.DetHeuristic.time_homogeneous_ratio_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:36:46.950052+00:00
-- url     : https://prove2.me/theorems/78eb3ffd-3699-46a3-ab45-1dbb5cdac541
-- title:
--   Proposition 8, eq. (36) — time-homogeneous case: one price is optimal and loses at most $\nu(C_0)/2$
-- statement:
--   Consider the $N$-period pricing model ($N \ge 1$) under the hypotheses of Proposition 8: for every $n$, $p \mapsto p\,E[D_n(p)]$ is concave and $p \mapsto E[D_n(p)]$ is convex on $[0,\infty)$; some $p^\infty \ge 0$ has $\sum_n E[D_n(p^\infty)] < C_0$; the deterministic problem (32)–(33) has an optimal solution $p^{\det}$ with $V_1^{\det}(C_0) > 0$. Assume in addition the time-homogeneous case
--   $$
--   E[D_n(p)] = T_n\,\lambda(p) \qquad (p \ge 0),
--   $$
--   with period durations $T_n > 0$ and a time-invariant intensity $\lambda$, and that every demand $D_n(p)$, $p \ge 0$, has finite variance. Then there is a single price $\bar p$ such that the constant vector $(\bar p, \dots, \bar p)$ solves (32)–(33), and for every such optimal single price $\bar p$, charging $\bar p$ in every period gives
--   $$
--   1 \ge \frac{V_1(\bar p, C_0)}{V_1(C_0)} \ge 1 - \frac{\nu(C_0)}{2},
--   $$
--   where $\nu(C_0) = \sigma_N / E[\mathscr{D}_N]$ is the coefficient of variation of the cumulative demand $\mathscr{D}_N = \sum_{n=1}^N D_n(\bar p)$ over the whole horizon.
--
--   In the time-homogeneous case the guarantee of Proposition 8 simplifies to a single coefficient of variation, and the optimal deterministic policy needs no price changes.
--
--   **Formalization Note** "A single price $p^{\det}$ solves (32)–(33)" is part of the conclusion, as an existential over $\bar p$, and the ratio bound is stated for every optimal single price (the heuristic charges the deterministic solution, whichever it is); existence of some optimal solution of (32)–(33) is a hypothesis, as in the goal. Finite variance is assumed at all nonnegative prices because $\bar p$ is produced by the theorem. $\nu(C_0)$ is `cumCV` at the last period, $V_1(\bar p, C_0)$ is `heuristicRevenue` at the constant vector.
-- source:
--   Bitran and Caldentey, An Overview of Pricing Models for Revenue Management, MSOM 5(3) 2003, p. 222, Proposition 8, eq. (36)

import Mathlib
import Definitions.Def_PricingRM_DetHeuristic_PricingModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PricingRM.DetHeuristic

/-- Bitran–Caldentey (2003), Proposition 8, eq. (36), p. 222 (time-homogeneous case): if
`E[D_n(p)] = T_n λ(p)` for all `p ≥ 0` with durations `T_n > 0`, then a single price `p̄`
solves (32)–(33), and charging any such optimal single price in every period gives
`1 ≥ V_1(p̄, C₀) / V_1(C₀) ≥ 1 - ν(C₀)/2`, where `ν(C₀)` is the coefficient of variation of
the cumulative demand `𝒟_N` over the whole horizon. -/
theorem time_homogeneous_ratio_bound {N : ℕ} (M : PricingModel N) (hN : 0 < N)
    (hconc : ∀ n, ConcaveOn ℝ (Set.Ici 0) (fun p => p * meanDemand M n p))
    (hconv : ∀ n, ConvexOn ℝ (Set.Ici 0) (meanDemand M n))
    (C₀ : ℝ) (hslater : ∃ pinf : ℝ, 0 ≤ pinf ∧ ∑ n, meanDemand M n pinf < C₀)
    (T : Fin N → ℝ) (hT : ∀ n, 0 < T n) (lam : ℝ → ℝ)
    (hhom : ∀ n, ∀ p : ℝ, 0 ≤ p → meanDemand M n p = T n * lam p)
    (hL2 : ∀ n, ∀ p : ℝ, 0 ≤ p → MemLp (fun x : ℝ => x) 2 (M.μ n p))
    (pdet : Fin N → ℝ) (hopt : IsDetOptimal M C₀ pdet)
    (hVdet : 0 < detObjective M pdet) :
    (∃ pbar : ℝ, IsDetOptimal M C₀ (fun _ => pbar)) ∧
      ∀ pbar : ℝ, IsDetOptimal M C₀ (fun _ => pbar) →
        1 ≥ heuristicRevenue M C₀ (fun _ => pbar) / (optValue M C₀).toReal ∧
        heuristicRevenue M C₀ (fun _ => pbar) / (optValue M C₀).toReal ≥
          1 - cumCV M (fun _ => pbar) ⟨N - 1, by omega⟩ / 2 := by sorry

end PricingRM.DetHeuristic
