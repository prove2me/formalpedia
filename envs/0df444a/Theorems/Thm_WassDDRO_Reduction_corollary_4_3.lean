-- Prove2me | Theorems.Thm_WassDDRO_Reduction_corollary_4_3
-- name    : WassDDRO.Reduction.corollary_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:44:24.653284+00:00
-- url     : https://prove2.me/theorems/4cd1adf3-8fb5-441a-b4a6-fc79d541b461
-- title:
--   Corollary 4.3, p. 14 — (10) ≤ optimal value of (12f) for any ε ≥ 0, without Assumption 4.1
-- statement:
--   Let $E$ be a finite-dimensional real normed space with its Borel σ-algebra and dual norm $\|\cdot\|_*$, $\Xi\subseteq E$, measurable $\ell_1,\dots,\ell_K:E\to\overline{\mathbb R}$ ($K\ge1$) with $\ell=\max_k\ell_k$, samples $\hat\xi_1,\dots,\hat\xi_N\in\Xi$ ($N\ge1$) and $\varepsilon\ge0$. Then the worst-case expectation (10) is at most the optimal value of the finite convex program (12f):
--   $$\sup_{\mathbb Q\in\mathbb B_\varepsilon(\widehat{\mathbb P}_N)}\mathbb E^{\mathbb Q}[\ell(\xi)]\;\le\;\left\{\begin{array}{ll}\inf\limits_{\lambda,s_i,z_{ik}}&\lambda\varepsilon+\frac1N\sum_{i=1}^N s_i\\ \text{s.t.}&[-\ell_k+\chi_\Xi]^*(z_{ik})-\langle z_{ik},\hat\xi_i\rangle\le s_i\quad\forall i\le N,\ \forall k\le K\\ &\|z_{ik}\|_*\le\lambda\quad\forall i\le N,\ \forall k\le K.\end{array}\right.$$
--   No convexity of $\Xi$ or of the $-\ell_k$ is assumed.
--
--   This gives a computable conservative bound on the worst-case expectation for arbitrary piecewise losses.
--
--   **Formalization Note** Here $[-\ell_k+\chi_\Xi]^*(z)=\sup_{\xi\in\Xi}\big(\langle z,\xi\rangle+\ell_k(\xi)\big)$, which is the paper's reading of the sum under $\infty-\infty=\infty$ (no `EReal` addition is performed). The infimum is $+\infty$ when (12f) is infeasible.
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, Corollary 4.3, p. 14; program (12f), p. 13

import Mathlib
import Definitions.Def_WassDDRO_Reduction_Setting

open MeasureTheory Filter Topology

namespace WassDDRO.Reduction

/-- Corollary 4.3 (Approximate convex reduction), p. 14: for any `ε ≥ 0`, without
Assumption 4.1, the worst-case expectation (10) is at most the optimal value of (12f). -/
theorem corollary_4_3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ) ≤ program12fValue ε Ξ ξhat ℓ := by sorry

end WassDDRO.Reduction
