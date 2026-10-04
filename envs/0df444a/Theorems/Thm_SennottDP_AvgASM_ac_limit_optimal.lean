-- Prove2me | Theorems.Thm_SennottDP_AvgASM_ac_limit_optimal
-- name    : SennottDP.AvgASM.ac_limit_optimal
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-01T10:06:38.758839+00:00
-- url     : https://prove2.me/theorems/e29ef934-313e-4c8a-ada0-66874bbca3cb
-- title:
--   Theorem 8.1.1 — under (AC), lim J^N is the minimum average cost and limit points of optimal policies are optimal
-- statement:
--   Let $\Delta$ be an MDC on a countable state space $S$ and $(\Delta_N)_{N\ge N_0}$ an approximating sequence for $\Delta$. Assume the (AC) assumptions hold for the constants $J^N$ and functions $r^N$ of (AC1), which satisfy
--   $$J^N+r^N(i)=\min_a\Big\{C(i,a)+\sum_{j\in S_N}P_{ij}(a;N)\,r^N(j)\Big\},\qquad i\in S_N. \tag{8.1}$$
--   Then:
--   1. the limit $J^*=\lim_{N\to\infty}J^N$ exists and is the minimum average cost in $\Delta$: $J(i)=J^*$ for every $i\in S$;
--   2. if, for each $N$, $e^N$ is a stationary policy for $\Delta_N$ realizing the minimum in (8.1), then every limit point $e^*$ of $(e^N)$ is an average cost optimal stationary policy for $\Delta$.
--
--   This is the main result of the chapter: it justifies computing an average cost optimal policy for a denumerable-state model by solving the average cost optimality equation of finite truncations.
--
--   **Formalization Note** The minimum average cost $J(i)$ is an infimum over all general policies, valued in $[0,\infty]$; its equality with the real number $J^*$ is stated in `EReal`, which also asserts that $J(i)$ is finite. The minimizing policies $e^N$ are given by their values on $S_N$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 169, Theorem 8.1.1

import Mathlib
import Definitions.Def_SennottDP_AvgASM_Assumptions

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.AvgASM

/-- **Theorem 8.1.1** (Sennott 1999, p. 169). Let `Δ` be an MDC on a countable state space `S` and
`(Δ_N)_{N ≥ N₀}` an approximating sequence for `Δ`. Assume that the (AC) assumptions hold for
the constants `J^N` and functions `r^N` of (AC1). Then:
(i) `J* = lim_{N→∞} J^N` exists and is the minimum average cost in `Δ`: `J(i) = J*` for all `i`;
(ii) any limit point `e*` of a sequence `e^N` of stationary policies realizing the minimum in
(8.1) is average cost optimal for `Δ`. -/
theorem ac_limit_optimal {S : Type*} {Act : Type*} [Countable S] {M : MDC S Act}
    (AS : ApproxSeq M) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hAC : AS.AC JN rN) :
    (∃ Jstar : ℝ, Tendsto JN atTop (𝓝 Jstar) ∧
        ∀ i, ((avgValue M i : ℝ≥0∞) : EReal) = (Jstar : EReal)) ∧
    ∀ e : ℕ → S → Act, AS.IsStationarySeq e →
      (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, JN N + rN N i = AS.acoeTerm rN N i (e N i)) →
      ∀ f : StationaryPolicy M, AS.IsLimitPoint e f → IsAverageOptimal f.toPolicy := by sorry

end SennottDP.AvgASM
