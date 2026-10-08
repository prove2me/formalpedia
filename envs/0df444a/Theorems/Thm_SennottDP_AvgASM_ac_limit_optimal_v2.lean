-- Prove2me | Theorems.Thm_SennottDP_AvgASM_ac_limit_optimal_v2
-- name    : SennottDP.AvgASM.ac_limit_optimal_v2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:00:28.397015+00:00
-- url     : https://prove2.me/theorems/8ed18c16-f644-4d35-99d2-f5e28b8958f3
-- title:
--   Theorem 8.1.1 (corrected: uniform lower bound in (AC3)): lim J^N is the minimum average cost, limit points of optimal policies are optimal
-- statement:
--   Corrected version (v2) of Theorem 8.1.1 (p. 169) of Sennott, *Stochastic Dynamic Programming and the Control of Queueing Systems*.
--
--   Let $\Delta$ be an MDC on a countable state space $S$ and $(\Delta_N)_{N\ge N_0}$ an approximating sequence for $\Delta$. Assume the (AC) assumptions hold for the constants $J^N$ and functions $r^N$ of (AC1), which satisfy
--   $$J^N+r^N(i)=\min_a\Big\{C(i,a)+\sum_{j\in S_N}P_{ij}(a;N)\,r^N(j)\Big\},\qquad i\in S_N, \tag{8.1}$$
--   and assume in addition that the lower bound of (AC3) holds **uniformly**: there is a constant $Q\ge0$ with $r^N(i)\ge -Q$ for all $i\in S_N$ and $N\ge N_0$. Then:
--   1. the limit $J^*=\lim_{N\to\infty}J^N$ exists and is the minimum average cost in $\Delta$: $J(i)=J^*$ for every $i\in S$;
--   2. if, for each $N$, $e^N$ is a stationary policy for $\Delta_N$ realizing the minimum in (8.1), then every limit point $e^*$ of $(e^N)$ is an average cost optimal stationary policy for $\Delta$.
--
--   **Formalization Note** The book states (AC3) only as $-Q\le\liminf_{N\to\infty}r^N(i)$ for each $i\in S$, and the first version of this theorem followed it; a counterexample (absorbing states, with $r^N$ very negative at the newest state $N$ of $S_N$) was accepted on prove2.me. The book's proof applies the bound $r^N\ge-Q$ uniformly, so this version adds that hypothesis and leaves the rest unchanged. The minimum average cost $J(i)$ is an infimum over all general policies, valued in $[0,\infty]$; its equality with the real number $J^*$ is stated in `EReal`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 169, Theorem 8.1.1 and (AC1)-(AC4); proof pp. 169-171

import Mathlib
import Definitions.Def_SennottDP_AvgASM_Assumptions

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.AvgASM

/-- **Theorem 8.1.1** (Sennott 1999, p. 169), corrected: (AC3) is used **uniformly**. The book states
(AC3) as `−Q ≤ liminf_{N→∞} r^N(i)` for each fixed `i`, but its proof uses the bound `r^N(i) ≥ −Q`
for all `i ∈ S_N` and `N ≥ N₀`; with only the pointwise `liminf` bound the statement is false
(a counterexample was accepted on prove2.me against `SennottDP.AvgASM.ac_limit_optimal`). The
hypothesis `hQ` adds that uniform bound; the conclusions are unchanged:
(i) `J* = lim_{N→∞} J^N` exists and is the minimum average cost in `Δ`: `J(i) = J*` for all `i`;
(ii) any limit point `e*` of a sequence `e^N` of stationary policies realizing the minimum in
(8.1) is average cost optimal for `Δ`. -/
theorem ac_limit_optimal_v2 {S : Type*} {Act : Type*} [Countable S] {M : MDC S Act}
    (AS : ApproxSeq M) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hAC : AS.AC JN rN)
    (hQ : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, -Q ≤ rN N i) :
    (∃ Jstar : ℝ, Tendsto JN atTop (𝓝 Jstar) ∧
        ∀ i, ((avgValue M i : ℝ≥0∞) : EReal) = (Jstar : EReal)) ∧
    ∀ e : ℕ → S → Act, AS.IsStationarySeq e →
      (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, JN N + rN N i = AS.acoeTerm rN N i (e N i)) →
      ∀ f : StationaryPolicy M, AS.IsLimitPoint e f → IsAverageOptimal f.toPolicy := by sorry

end SennottDP.AvgASM
