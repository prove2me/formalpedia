-- Prove2me | Theorems.Thm_SennottDP_AvgFiniteVI_prop_6_6_6_transform_value_iteration
-- name    : SennottDP.AvgFiniteVI.prop_6_6_6_transform_value_iteration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T09:32:13.747309+00:00
-- url     : https://prove2.me/theorems/405b28d7-1bee-45cd-91fb-e47f7c3d66d5
-- title:
--   Proposition 6.6.6 — value iteration on the transformed MDC solves the ACOE of the original
-- statement:
--   Let $\Delta$ be an MDC with finite state space $S$ whose minimum average cost is constant, and let $\Delta^*$ be its transformation (6.64) with $0 < \tau < 1$. Then the minimum average cost of $\Delta^*$ is a constant $J^*$ and Assumption OPA holds for $\Delta^*$. Hence Proposition 6.6.3 applies to $\Delta^*$: for any distinguished state $x$, $v^*_n(x) - v^*_{n-1}(x) \to J^*$ and $r^*_n \to r^*$. The pair $(J^*/\tau, r^*)$ satisfies
--   $$\frac{J^*}{\tau} + r^*(i) = \min_a\Big\{C(i,a) + \sum_j P_{ij}(a) r^*(j)\Big\}, \qquad i \in S,$$
--   the ACOE (6.37) of $\Delta$, and hence every stationary policy realizing this minimum is average cost optimal for $\Delta$.
--
--   This is how value iteration is used when Assumption OPA may fail.
--
--   **Formalization Note** $J^*$ here is the constant minimum average cost of $\Delta^*$, not the lim inf average cost $J^*(i)$ of Section 2.4; in Lean it is named `Jt`, and $r^*$ is `rt`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 121, Proposition 6.6.6; p. 122, Eq. (6.65)

import Mathlib
import Definitions.Def_SennottDP_AvgFiniteVI_ACOE
import Definitions.Def_SennottDP_AvgFiniteVI_Transform

namespace SennottDP.AvgFiniteVI

open scoped ENNReal NNReal Topology
open Filter

/-- Proposition 6.6.6 (Sennott, p. 121). Let `S` be finite, assume that the minimum average cost
in `Δ` is a constant, and let `Δ*` be the aperiodicity transformation (6.64) with `0 < τ < 1`.
Then the minimum average cost in `Δ*` is a constant `J*` and Assumption OPA holds for `Δ*`. Hence
Proposition 6.6.3 applies to `Δ*`: for any distinguished state `x`, `v*_n(x) − v*_{n−1}(x) → J*` and
`r*_n → r*`. The pair `(J*/τ, r*)` satisfies (6.37) for `Δ`, and hence every stationary policy
realizing the minimum there is average cost optimal for `Δ`. (`J*` is the minimum average cost of
`Δ*`, not the lim inf average cost of Section 2.4.) -/
theorem prop_6_6_6_transform_value_iteration {S : Type*} {Act : Type*} [Fintype S]
    (M : MDC S Act) (hconst : ∃ J : ℝ≥0∞, ∀ i : S, avgValue M i = J)
    (τ : ℝ≥0) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    let M' := transform M τ hτ1.le
    (∃ Jt : ℝ≥0, ∀ i : S, avgValue M' i = Jt) ∧
    AssumptionOPA M' ∧
    ∀ Jt : ℝ≥0, (∀ i : S, avgValue M' i = Jt) → ∀ x : S,
      Tendsto (fun n : ℕ => (horizonValue M' (n + 1) x).toReal - (horizonValue M' n x).toReal)
          atTop (𝓝 (Jt : ℝ)) ∧
      ∃ rt : S → ℝ,
        (∀ i : S, Tendsto (fun n : ℕ => relHorizon M' x n i) atTop (𝓝 (rt i))) ∧
        (∀ i : S, (Jt : ℝ) / τ + rt i = bellmanMin M rt i) ∧
        ∀ e : StationaryPolicy M, RealizesMin M rt e → IsAverageOptimal e.toPolicy := by sorry

end SennottDP.AvgFiniteVI
