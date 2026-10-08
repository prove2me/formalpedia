-- Prove2me | Theorems.Thm_TDApprox_Conv_lemma_1
-- name    : TDApprox.Conv.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:41.987193+00:00
-- url     : https://prove2.me/theorems/667c34ca-38f9-4336-9ccb-3307507af9bc
-- title:
--   Lemma 1, p. 12 — ‖PJ‖_D ≤ ‖J‖_D for every J ∈ L₂(S, D)
-- statement:
--   Let $P = (p_{ij})$ be the transition matrix of a Markov chain on a countable state space $S$, and suppose that the chain has a unique invariant distribution $\pi$ with $\pi(i) > 0$ for every $i$ (Assumption 1(a)). Write $\|J\|_D^2 = \sum_i \pi(i)J(i)^2$, so that $L_2(S,D) = \{J : \|J\|_D < \infty\}$, and $(PJ)(i) = \sum_j p_{ij}J(j)$.
--
--   For every $J \in L_2(S,D)$, the vector $PJ$ is well defined (each series $\sum_j p_{ij}J(j)$ converges absolutely), lies in $L_2(S,D)$, and
--   $$\|PJ\|_D \le \|J\|_D.$$
--
--   So $P$ is a nonexpansion of the steady-state weighted norm. Every contraction estimate of the paper (Lemmas 2–5) rests on this inequality.
--
--   **Formalization Note.** $(PJ)(i)$ is the integral of $J$ against the row $P(i)$. The well-definedness of $PJ$ and its membership in $L_2(S,D)$ are added as conjuncts; the page uses both implicitly when it writes $\|PJ\|_D$.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Lemma 1, p. 12

import Mathlib
import Definitions.Def_TDApprox_Conv_Model
open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix

namespace TDApprox.Conv

/-- **Lemma 1** (Tsitsiklis & Van Roy, LIDS-P-2322 (1996), p. 12). Under Assumption 1(a), for any
`J ∈ L₂(S, D)` we have `‖PJ‖_D ≤ ‖J‖_D`, where `(PJ)(i) = Σ_j p_ij J(j) = ∫ J d(P i)`.
The conclusion also records that `PJ` is well defined (`J` is integrable under every row `P i`)
and lies in `L₂(S, D)`; both are implicit in the page's `‖PJ‖_D`. -/
theorem lemma_1 {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (h1a : Assumption1a P π) (J : S → ℝ) (hJ : MemL2D π J) :
    (∀ i, Integrable J (P i)) ∧ MemL2D π (Pop P J) ∧ normD π (Pop P J) ≤ normD π J := by sorry

end TDApprox.Conv
