-- Prove2me | Theorems.Thm_WassDDRO_Reduction_worstCase_le_program12c
-- name    : WassDDRO.Reduction.worstCase_le_program12c
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:40:15.862027+00:00
-- url     : https://prove2.me/theorems/ff155b60-6b4d-49de-bc21-a40303210245
-- title:
--   Proof of Theorem 4.2, (12a)–(12c), p. 12 — the worst-case expectation is at most the value of (12c)
-- statement:
--   Let $E$ be a finite-dimensional real normed space with its Borel σ-algebra, $\Xi\subseteq E$, and let $\ell_1,\dots,\ell_K:E\to\overline{\mathbb R}$ ($K\ge1$) be measurable, with $\ell=\max_k\ell_k$. Let $\hat\xi_1,\dots,\hat\xi_N\in\Xi$ ($N\ge 1$) be samples with empirical distribution $\widehat{\mathbb P}_N$, and let $\varepsilon\ge 0$. Then, without any convexity assumption,
--   $$\sup_{\mathbb Q\in\mathbb B_\varepsilon(\widehat{\mathbb P}_N)}\mathbb E^{\mathbb Q}[\ell(\xi)]\;\le\;\left\{\begin{array}{ll}\inf\limits_{\lambda,s_i}&\lambda\varepsilon+\frac1N\sum_{i=1}^N s_i\\ \text{s.t.}&\sup_{\xi\in\Xi}\big(\ell(\xi)-\lambda\|\xi-\hat\xi_i\|\big)\le s_i\quad\forall i\le N\\ &\lambda\ge 0.\end{array}\right.$$
--
--   This is the weak-duality half of the reduction: the right-hand side is (12c), the epigraph form of (12b), obtained from (10) by the max-min inequality (12a).
--
--   **Formalization Note** The expectation follows the paper's extended-arithmetic convention ($\infty-\infty=\infty$); the infimum is $+\infty$ when (12c) is infeasible. The sample condition $\hat\xi_i\in\Xi$ and measurability of the $\ell_k$ are the paper's standing assumptions (§2, p. 5; p. 11).
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, proof of Theorem 4.2, (12a), (12b), (12c), p. 12

import Mathlib
import Definitions.Def_WassDDRO_Reduction_Setting

open MeasureTheory Filter Topology

namespace WassDDRO.Reduction

/-- Proof of Theorem 4.2, (12a)–(12c), p. 12: without Assumption 4.1, the worst-case
expectation (10) is at most the optimal value of (12c). -/
theorem worstCase_le_program12c {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ) ≤ program12cValue ε Ξ ξhat (maxLoss ℓ) := by sorry

end WassDDRO.Reduction
