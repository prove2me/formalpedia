-- Prove2me | Theorems.Thm_SennottDP_ContinuousTime_asm_optimal_ctmdc
-- name    : SennottDP.ContinuousTime.asm_optimal_ctmdc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T11:20:52.888084+00:00
-- url     : https://prove2.me/theorems/fc7d25b4-d83d-4015-ad84-b4bb51b1a786
-- title:
--   Theorem 10.3.3 — approximating sequences for the auxiliary MDC compute average cost optimal policies of a CTMDC
-- statement:
--   Let $\Psi$ be a CTMDC on a countable state space satisfying Assumption (CTB) with constants $\tau$ and $B$, and let $\Delta$ be its auxiliary MDC built with $\tau$, such that Assumption (CTAC) holds: $J^\Delta(i)\le J^\Psi(i)$ for all $i$. Let $(\Delta_N)_{N\ge N_0}$ be an approximating sequence for $\Delta$ satisfying the (AC) assumptions with constants $J^N$ and functions $r^N$, so that
--
--   $$J^N+r^N(i)=\min_{a}\Big\{C(i,a)+\sum_{j\in S_N}P^*_{ij}(a;N)\,r^N(j)\Big\},\qquad i\in S_N,\ N\ge N_0.$$
--
--   Then:
--
--   1. the limit $J^*=\lim_{N\to\infty}J^N$ exists, and $J^*$ is the minimum average cost in both $\Delta$ and $\Psi$: $J^\Delta(i)=J^\Psi(i)=J^*$ for every $i\in S$;
--   2. if $e^N$ is a sequence of stationary policies realizing the minimum in the display above and $e^*$ is a limit point of $(e^N)$, then $e^*(i)\in A_i$ for all $i$ and $e^*$ is average cost optimal for both $\Delta$ and $\Psi$: $J^\Delta_{e^*}(i)=J^\Delta(i)$ and $J^\Psi_{e^*}(i)=J^\Psi(i)$ for every $i\in S$.
--
--   The theorem makes average cost optimal control of a continuous time chain computable: a finite state approximation of a discrete time chain yields the optimal average cost and an optimal stationary policy of the original continuous time chain.
--
--   **Formalization Note** The optimal costs $J^\Delta$, $J^\Psi\in[0,\infty]$ are compared with the real limit $J^*$ in `EReal`. The page prints the index set of the sum as $j\in S_n$; it is $S_N$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 246, Theorem 10.3.3, eq. (10.21)

import Mathlib
import Definitions.Def_SennottDP_ContinuousTime_ApproxSeq
import Definitions.Def_SennottDP_ContinuousTime_CTMDC

open scoped ENNReal
open Filter Topology

namespace SennottDP.ContinuousTime

/-- Theorem 10.3.3 (p. 246). -/
theorem asm_optimal_ctmdc {S Act : Type} [Countable S] (Ψ : CTMDC S Act) (hΨ : Ψ.IsValid)
    (tau B : ℝ) (hCTB : Ψ.CTB tau B) (hCTAC : Ψ.CTAC tau)
    (Δs : ApproxSeq (Ψ.aux tau)) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hAC : Δs.AC JN rN) :
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
