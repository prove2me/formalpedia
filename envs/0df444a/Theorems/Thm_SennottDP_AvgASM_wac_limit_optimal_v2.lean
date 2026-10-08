-- Prove2me | Theorems.Thm_SennottDP_AvgASM_wac_limit_optimal_v2
-- name    : SennottDP.AvgASM.wac_limit_optimal_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:09.295977+00:00
-- url     : https://prove2.me/theorems/17456e85-7c92-482d-95b1-ebd1450b1744
-- title:
--   Proposition 8.7.1 (corrected: uniform lower bound in (WAC3)) — under (WAC) the conclusions of Theorem 8.1.1 hold
-- statement:
--   Corrected version (v2) of Proposition 8.7.1 (p. 194) of Sennott, *Stochastic Dynamic Programming and the Control of Queueing Systems*.
--
--   Let $(\Delta_N)_{N\ge N_0}$ be an approximating sequence for the MDC $\Delta$ on a countable state space, and let the constants $J^N$ and functions $r^N$ satisfy the (WAC) assumptions: (WAC1), (WAC2), (WAC4) are (AC1), (AC2), (AC4) — the optimality equations
--   $$J^N+r^N(i)=\min_a\Big\{C(i,a)+\sum_{j\in S_N}P_{ij}(a;N)\,r^N(j)\Big\},\qquad i\in S_N,\tag{8.1}$$
--   $\limsup_Nr^N(i)<\infty$ and $\limsup_NJ^N=:J^*<\infty$ with $J^*\le J(i)$ — and (WAC3): there is a nonnegative function $Q$ on $S$ with $-Q(i)\le\liminf_Nr^N(i)=:u(i)$ for all $i$ such that, for every stationary policy $e$ and initial state $i$, (i) $\lim_N\sum_{j\in S_N}P_{ij}(e;N)Q(j)=\sum_jP_{ij}(e)Q(j)<\infty$, (ii) $E_e[u(X_n)]>-\infty$ for $n\ge1$, and (iii) $\liminf_nE_e[u(X_n)]/n\ge0$. Assume in addition that the lower bound of (WAC3) holds **uniformly**: for a nonnegative function $Q$ satisfying (i), $r^N(j)\ge-Q(j)$ for all $j\in S_N$ and all $N\ge N_0$. Then the conclusions of Theorem 8.1.1 are valid:
--   1. the limit $J^*=\lim_{N\to\infty}J^N$ exists and is the minimum average cost in $\Delta$, i.e. $J(i)=J^*$ for all $i\in S$;
--   2. any limit point $e^*$ of a sequence $e^N$ of stationary policies realizing the minimum in (8.1) is average cost optimal for $\Delta$.
--
--   Since (AC) implies (WAC) (take $Q(\cdot)\equiv Q$), this is a strengthening of Theorem 8.1.1 that allows the lower bound on the relative values to depend on the state.
--
--   **Formalization Note.** The book states (WAC3) only through the pointwise $\liminf$ bound $-Q(i)\le\liminf_Nr^N(i)$ for each $i$, and the retired version followed it; its proof, however, passes to the limit in (8.1) by a Fatou-type argument that applies $r^N(j)+Q(j)\ge0$ to every $j\in S_N$ and every $N\ge N_0$ together with (WAC3₂)(i) for the same $Q$. With only the pointwise bound the statement is false: the counterexample accepted on prove2.me (every state absorbing, $r^N$ very negative at the newest state $N$ of $S_N$) satisfies (WAC) and refutes conclusion 1; the same example refuted Theorem 8.1.1 as first stated, which has been replaced by `SennottDP.AvgASM.ac_limit_optimal_v2`. Consistently with that replacement, this version keeps `AS.WAC JN rN` as in the original definition module `Def_SennottDP_AvgASM_Assumptions` and adds the uniform bound as the explicit hypothesis `hQ`, for a nonnegative $Q:S\to[0,\infty)$ that also satisfies the convergence and finiteness condition (WAC3₂)(i); the conclusions are unchanged. The minimum average cost $J(i)$ is an infimum over all general policies, valued in $[0,\infty]$; its equality with the real number $J^*$ is stated in `EReal`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 194, Proposition 8.7.1 and (WAC), pp. 193–194; p. 169, Theorem 8.1.1 and (AC1)–(AC4), proof pp. 169–171 — the lower bound of (WAC3) is used uniformly in N (as in the book's proof), not only through the printed pointwise liminf

import Mathlib
import Definitions.Def_SennottDP_AvgASM_Assumptions

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.AvgASM

/-- **Proposition 8.7.1** (Sennott 1999, p. 194), corrected: (WAC3) is used **uniformly**. The
book states (WAC3₁) as `−Q(i) ≤ liminf_{N→∞} r^N(i)` for each fixed `i`, but the proof passes
to the limit in (8.1) by a Fatou argument that uses the bound `r^N(j) ≥ −Q(j)` for all `j ∈ S_N`
and all `N ≥ N₀`, together with (WAC3₂)(i) for the same `Q`; with only the pointwise `liminf`
bound the statement is false (the counterexample accepted on prove2.me against
`SennottDP.AvgASM.wac_limit_optimal`, which also refuted Theorem 8.1.1 as first stated; see
`ac_limit_optimal_v2`). The hypothesis `hQ` adds that uniform bound, for a nonnegative function
`Q` satisfying (WAC3₂)(i); the conclusions are unchanged:
`lim_{N→∞} J^N` exists and equals the (constant) minimum average cost `J(i)` of `Δ`, and any
limit point of a sequence of stationary policies realizing the minimum in (8.1) is average cost
optimal for `Δ`. -/
theorem wac_limit_optimal_v2 {S : Type*} {Act : Type*} [Countable S] {M : MDC S Act}
    (AS : ApproxSeq M) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hWAC : AS.WAC JN rN)
    (hQ : ∃ Q : S → ℝ≥0,
      (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, -(Q i : ℝ) ≤ rN N i) ∧
      ∀ e : StationaryPolicy M, ∀ i,
        Tendsto (fun N => ∑ j ∈ AS.SN N, AS.PN N i (e.f i) j * (Q j : ℝ≥0∞)) atTop
          (𝓝 (∑' j, M.P i (e.f i) j * (Q j : ℝ≥0∞))) ∧
        ∑' j, M.P i (e.f i) j * (Q j : ℝ≥0∞) < ⊤) :
    (∃ Jstar : ℝ, Tendsto JN atTop (𝓝 Jstar) ∧
        ∀ i, ((avgValue M i : ℝ≥0∞) : EReal) = (Jstar : EReal)) ∧
    ∀ e : ℕ → S → Act, AS.IsStationarySeq e →
      (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, JN N + rN N i = AS.acoeTerm rN N i (e N i)) →
      ∀ f : StationaryPolicy M, AS.IsLimitPoint e f → IsAverageOptimal f.toPolicy := by sorry

end SennottDP.AvgASM
