-- Prove2me | Theorems.Thm_SennottDP_AvgFiniteVI_prop_6_6_3_value_iteration
-- name    : SennottDP.AvgFiniteVI.prop_6_6_3_value_iteration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T09:32:00.01798+00:00
-- url     : https://prove2.me/theorems/930e92b5-12f6-400c-8897-2e695fc2d81b
-- title:
--   Proposition 6.6.3 — finite horizon value iteration converges to a solution of the ACOE under OPA
-- statement:
--   Let $\Delta$ be an MDC with finite state space $S$. Assume the minimum average cost is a constant $J$ and Assumption OPA holds (every positive recurrent class of every average cost optimal stationary policy is aperiodic). Let $x \in S$ be any distinguished state, $v_n$ the minimum $n$-horizon expected cost with terminal cost $0$, and $r_n(i) = v_n(i) - v_n(x)$, so that
--   $$[v_n(x) - v_{n-1}(x)] + r_n(i) = \min_a\Big\{C(i,a) + \sum_j P_{ij}(a) r_{n-1}(j)\Big\}, \qquad n \ge 1,\ i \in S. \tag{6.49}$$
--   Let $f_n$ be finite horizon optimal stationary policies (each $f_n$ realizes the minimum in (6.49)). Then
--   $$\lim_{n\to\infty} [v_n(x) - v_{n-1}(x)] = J, \qquad \lim_{n\to\infty} r_n(i) =: r(i) \text{ exists},$$
--   the pair $(J, r)$ solves the ACOE
--   $$J + r(i) = \min_a\Big\{C(i,a) + \sum_j P_{ij}(a) r(j)\Big\}, \qquad i \in S, \tag{6.37}$$
--   and every limit point of $(f_n)$ realizes the minimum in (6.37) and is average cost optimal.
--
--   This justifies the value iteration algorithm 6.6.4 for computing the minimum average cost and an optimal stationary policy.
--
--   **Formalization Note** $f_n$ is taken to realize the minimum in $v_n(i) = \min_a\{C(i,a) + \sum_j P_{ij}(a) v_{n-1}(j)\}$, which has the same minimizers as (6.49); `fs (n+1)` is $f_{n+1}$ and `fs 0` is unused. Limit points are in the sense of Definition B.1.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 117, Proposition 6.6.3; p. 115, Eq. (6.49)

import Mathlib
import Definitions.Def_SennottDP_AvgFiniteVI_ACOE

namespace SennottDP.AvgFiniteVI

open scoped ENNReal NNReal Topology
open Filter

/-- Proposition 6.6.3 (Sennott, p. 117). Let `S` be finite, assume that the minimum average cost
is a constant `J` and that Assumption OPA holds, and let `x` be any distinguished state. Let `f_n`
(`n ≥ 1`) be finite horizon optimal stationary policies: `f_n` realizes the minimum in
`v_n(i) = min_a {C(i,a) + ∑_j P_{ij}(a) v_{n−1}(j)}` (3.2), equivalently in (6.49). Then
`lim_n [v_n(x) − v_{n−1}(x)] = J`, `lim_n r_n(i) =: r(i)` exists for every `i`, the pair `(J, r)`
solves the ACOE (6.37), and every limit point of `(f_n)` realizes the minimum in (6.37) and is
average cost optimal. -/
theorem prop_6_6_3_value_iteration {S : Type*} {Act : Type*} [Fintype S]
    (M : MDC S Act) (J : ℝ≥0) (hJ : ∀ i : S, avgValue M i = J) (hOPA : AssumptionOPA M)
    (x : S) (fs : ℕ → StationaryPolicy M)
    (hfs : ∀ n : ℕ, RealizesMin M (fun j => (horizonValue M n j).toReal) (fs (n + 1))) :
    Tendsto (fun n : ℕ => (horizonValue M (n + 1) x).toReal - (horizonValue M n x).toReal)
        atTop (𝓝 (J : ℝ)) ∧
    ∃ r : S → ℝ,
      (∀ i : S, Tendsto (fun n : ℕ => relHorizon M x n i) atTop (𝓝 (r i))) ∧
      (∀ i : S, (J : ℝ) + r i = bellmanMin M r i) ∧
      ∀ e : StationaryPolicy M, IsLimitPoint fs e →
        RealizesMin M r e ∧ IsAverageOptimal e.toPolicy := by sorry

end SennottDP.AvgFiniteVI
