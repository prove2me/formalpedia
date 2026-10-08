-- Prove2me | Theorems.Thm_TDApprox_Conv_lemma_3
-- name    : TDApprox.Conv.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:36.894746+00:00
-- url     : https://prove2.me/theorems/2ac5ee33-af68-476f-bb24-e06e1885e774
-- title:
--   Lemma 3, p. 13 — T^(λ) maps L₂(S, D) into itself, and T^(λ)J = (1−λ)Σ_m λ^m(Σ_{t≤m}(αP)^t ḡ + (αP)^{m+1}J) for λ < 1
-- statement:
--   Under Assumption 1 (the chain has a unique invariant distribution $\pi > 0$, $E_0[g^2] < \infty$, and every $J^*(i)$ is well defined and finite), let $\alpha \in (0,1)$, $\lambda \in [0,1]$ and $J \in L_2(S,D)$. Let $T^{(\lambda)}$ be the operator
--   $$(T^{(\lambda)}J)(i) = (1-\lambda)\sum_{m=0}^\infty \lambda^m E\Big[\sum_{t=0}^m \alpha^t g(i_t,i_{t+1}) + \alpha^{m+1}J(i_{m+1}) \,\Big|\, i_0 = i\Big]$$
--   for $\lambda < 1$, with $T^{(1)}J = J^*$.
--
--   Then $T^{(\lambda)}J \in L_2(S,D)$, every $(P^mJ)(i)$ is well defined, and for $\lambda \in [0,1)$
--   $$T^{(\lambda)}J = (1-\lambda)\sum_{m=0}^\infty \lambda^m\Big(\sum_{t=0}^m (\alpha P)^t\bar g + (\alpha P)^{m+1}J\Big),$$
--   where the series converges at every state.
--
--   The formula turns the expectation that defines $T^{(\lambda)}$ into an expression in $P$, $\bar g$ and $J$, which is what the contraction estimate of Lemma 4 and the steady-state identity of Lemma 7 use.
--
--   **Formalization Note.** The series is stated pointwise, with $((\alpha P)^t \bar g)(i) = \alpha^t \int \bar g \, d P^t(i)$, and the factor $(1-\lambda)$ is kept inside each term. At $\lambda = 0$ Lean's convention $0^0 = 1$ keeps only the term $m = 0$, as on the page.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Lemma 3, p. 13

import Mathlib
import Definitions.Def_TDApprox_Conv_Model
open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix

namespace TDApprox.Conv

/-- **Lemma 3** (Tsitsiklis & Van Roy, LIDS-P-2322 (1996), p. 13). Under Assumption 1, for any
`J ∈ L₂(S, D)` and `λ ∈ [0, 1]`, `T^(λ)J ∈ L₂(S, D)`, and for `λ ∈ [0, 1)`
`T^(λ)J = (1 − λ) Σ_{m ≥ 0} λ^m (Σ_{t=0}^m (αP)^t ḡ + (αP)^{m+1} J)`, the series converging at
every state (and every `(P^m J)(i)` being well defined). -/
theorem lemma_3 {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h1 : Assumption1 P π g α) (J : S → ℝ) (hJ : MemL2D π J)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    MemL2D π (Tlam P g α lam J) ∧
    (∀ i m, Integrable J ((P ^ m) i)) ∧
    (lam < 1 → ∀ i, HasSum
      (fun m : ℕ => (1 - lam) * lam ^ m *
        (∑ t ∈ range (m + 1), α ^ t * ∫ j, gbar P g j ∂((P ^ t) i) +
          α ^ (m + 1) * ∫ j, J j ∂((P ^ (m + 1)) i)))
      (Tlam P g α lam J i)) := by sorry

end TDApprox.Conv
