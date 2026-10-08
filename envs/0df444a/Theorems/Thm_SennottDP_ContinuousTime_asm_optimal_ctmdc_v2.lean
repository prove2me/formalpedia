-- Prove2me | Theorems.Thm_SennottDP_ContinuousTime_asm_optimal_ctmdc_v2
-- name    : SennottDP.ContinuousTime.asm_optimal_ctmdc_v2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:09:07.978639+00:00
-- url     : https://prove2.me/theorems/1ebebaa0-ef17-4c24-967c-8ce96e142fa0
-- title:
--   Theorem 10.3.3 (corrected: uniform lower bound in (AC3)): approximating sequences for the auxiliary MDC compute average cost optimal policies of a CTMDC
-- statement:
--   Corrected version (v2) of Theorem 10.3.3 (p. 246) of Sennott, *Stochastic Dynamic Programming and the Control of Queueing Systems*.
--
--   Let $\Psi$ be a CTMDC on a countable state space satisfying Assumption (CTB) with constants $\tau$ and $B$, and let $\Delta$ be its auxiliary MDC built with $\tau$, such that Assumption (CTAC) holds: $J^\Delta(i)\le J^\Psi(i)$ for all $i$. Let $(\Delta_N)_{N\ge N_0}$ be an approximating sequence for $\Delta$ satisfying the (AC) assumptions with constants $J^N$ and functions $r^N$, so that
--
--   $$J^N+r^N(i)=\min_{a}\Big\{C(i,a)+\sum_{j\in S_N}P^*_{ij}(a;N)\,r^N(j)\Big\},\qquad i\in S_N,\ N\ge N_0,$$
--
--   and assume in addition that the lower bound of (AC3) holds **uniformly**: there is a constant $Q\ge0$ with $r^N(i)\ge-Q$ for all $i\in S_N$ and $N\ge N_0$. Then:
--
--   1. the limit $J^*=\lim_{N\to\infty}J^N$ exists, and $J^*$ is the minimum average cost in both $\Delta$ and $\Psi$: $J^\Delta(i)=J^\Psi(i)=J^*$ for every $i\in S$;
--   2. if $e^N$ is a sequence of stationary policies realizing the minimum in the display above and $e^*$ is a limit point of $(e^N)$, then $e^*(i)\in A_i$ for all $i$ and $e^*$ is average cost optimal for both $\Delta$ and $\Psi$: $J^\Delta_{e^*}(i)=J^\Delta(i)$ and $J^\Psi_{e^*}(i)=J^\Psi(i)$ for every $i\in S$.
--
--   **Formalization Note** The book states (AC3) only as $-Q\le\liminf_{N\to\infty}r^N(i)$ for each $i$, and the first version of this theorem followed it; a counterexample (a state moving off to infinity with $r^N(N)=-N$) was accepted on prove2.me. The proof rests on Theorem 8.1.1, which applies the bound $r^N\ge-Q$ uniformly, so this version adds that hypothesis and leaves the rest unchanged (the same correction as `SennottDP.AvgASM.ac_limit_optimal_v2`). The optimal costs $J^\Delta$, $J^\Psi\in[0,\infty]$ are compared with the real limit $J^*$ in `EReal`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 246, Theorem 10.3.3, eq. (10.21); (AC1)-(AC4) p. 169

import Mathlib
import Definitions.Def_SennottDP_ContinuousTime_ApproxSeq
import Definitions.Def_SennottDP_ContinuousTime_CTMDC

open scoped ENNReal
open Filter Topology

namespace SennottDP.ContinuousTime

/-- Theorem 10.3.3 (p. 246), corrected: (AC3) is used **uniformly**. The book states (AC3) as
`−Q ≤ liminf_{N→∞} r^N(i)` for each fixed `i`, but the proof (through Theorem 8.1.1) uses the bound
`r^N(i) ≥ −Q` for all `i ∈ S_N` and `N ≥ N₀`; with only the pointwise bound the statement is false (a
counterexample was accepted on prove2.me against `SennottDP.ContinuousTime.asm_optimal_ctmdc`). The
hypothesis `hQ` adds that uniform bound; the conclusions are unchanged. -/
theorem asm_optimal_ctmdc_v2 {S Act : Type} [Countable S] (Ψ : CTMDC S Act) (hΨ : Ψ.IsValid)
    (tau B : ℝ) (hCTB : Ψ.CTB tau B) (hCTAC : Ψ.CTAC tau)
    (Δs : ApproxSeq (Ψ.aux tau)) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hAC : Δs.AC JN rN)
    (hQ : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, -Q ≤ rN N i) :
    (∃ Jstar : ℝ, Tendsto JN atTop (𝓝 Jstar) ∧
        ∀ i, (((Ψ.aux tau).avgValue i : ℝ≥0∞) : EReal) = (Jstar : EReal) ∧
          ((Ψ.avgValue i : ℝ≥0∞) : EReal) = (Jstar : EReal)) ∧
      ∀ (eN : ℕ → S → Act) (estar : S → Act),
        Δs.RealizesMin JN rN eN → Δs.IsLimitPoint eN estar →
          ∃ he : ∀ i, estar i ∈ Ψ.A i,
            (∀ i, (Ψ.aux tau).avgCost ((Ψ.aux tau).ofStationary estar he) i =
                (Ψ.aux tau).avgValue i) ∧
            ∀ i, Ψ.avgCost (Ψ.ofStationary estar he) i = Ψ.avgValue i := by sorry

end SennottDP.ContinuousTime
