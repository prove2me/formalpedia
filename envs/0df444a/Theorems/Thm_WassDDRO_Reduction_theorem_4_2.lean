-- Prove2me | Theorems.Thm_WassDDRO_Reduction_theorem_4_2
-- name    : WassDDRO.Reduction.theorem_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:49:26.751431+00:00
-- url     : https://prove2.me/theorems/bb21e393-0f3a-4cf6-b58c-1ff24b28858a
-- title:
--   Theorem 4.2, p. 12 — under Assumption 4.1, sup over the Wasserstein ball of E[max_k ℓ_k] equals the optimal value of the convex program (11)
-- statement:
--   Let $E$ be a finite-dimensional real normed space (the paper's $\mathbb R^m$ with an arbitrary norm $\|\cdot\|$) with its Borel σ-algebra, and $\|\cdot\|_*$ the dual norm. Let $\Xi\subseteq E$, let $\ell_1,\dots,\ell_K:E\to\overline{\mathbb R}$ ($K\ge1$) be measurable with $\ell(\xi)=\max_{k\le K}\ell_k(\xi)$, let $\hat\xi_1,\dots,\hat\xi_N\in\Xi$ ($N\ge1$) be samples with empirical distribution $\widehat{\mathbb P}_N=\frac1N\sum_i\delta_{\hat\xi_i}$, and let $\mathbb B_\varepsilon(\widehat{\mathbb P}_N)$ be the set of probability measures supported on $\Xi$ within 1-Wasserstein distance $\varepsilon$ of $\widehat{\mathbb P}_N$.
--
--   **Theorem 4.2 (Convex reduction).** If Assumption 4.1 holds ($\Xi$ convex and closed; each $-\ell_k$ proper, convex and lower semicontinuous; no $\ell_k$ identically $-\infty$ on $\Xi$), then for any $\varepsilon\ge0$
--   $$\sup_{\mathbb Q\in\mathbb B_\varepsilon(\widehat{\mathbb P}_N)}\mathbb E^{\mathbb Q}[\ell(\xi)]=\left\{\begin{array}{ll}\inf\limits_{\lambda,s_i,z_{ik},\nu_{ik}}&\lambda\varepsilon+\frac1N\sum_{i=1}^N s_i\\ \text{s.t.}&[-\ell_k]^*(z_{ik}-\nu_{ik})+\sigma_\Xi(\nu_{ik})-\langle z_{ik},\hat\xi_i\rangle\le s_i\quad\forall i\le N,\ \forall k\le K\\ &\|z_{ik}\|_*\le\lambda\quad\forall i\le N,\ \forall k\le K,\end{array}\right.$$
--   where $[-\ell_k]^*$ is the convex conjugate of $-\ell_k$ and $\sigma_\Xi$ the support function of $\Xi$.
--
--   The theorem turns an optimization over infinitely many probability distributions into a finite-dimensional convex program, which is what makes Wasserstein distributionally robust optimization tractable.
--
--   **Formalization Note** The expectation of an extended-valued function uses the paper's convention $\infty-\infty=\infty$, so a distribution with $\mathbb E^{\mathbb Q}[\max\{\ell,0\}]=\infty$ makes the supremum $+\infty$. The infimum of (11) is $+\infty$ when (11) is infeasible. $\langle z,\xi\rangle$ is the application of a continuous linear functional and $\|z\|_*$ its operator norm. The conditions $\hat\xi_i\in\Xi$, $N\ge1$, $K\ge1$ and measurability of the $\ell_k$ are the paper's standing setting (§2, p. 5; p. 11).
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, Theorem 4.2, p. 12; proof pp. 12–13

import Mathlib
import Definitions.Def_WassDDRO_Reduction_Setting

open MeasureTheory Filter Topology

namespace WassDDRO.Reduction

/-- Theorem 4.2 (Convex reduction), p. 12. Under Assumption 4.1, for any `ε ≥ 0` the
worst-case expectation (10) equals the optimal value of the finite convex program (11). -/
theorem theorem_4_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ)
    (ε : ℝ) (hε : 0 ≤ ε) (hA : Assumption41 Ξ ℓ) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ) = program11Value ε Ξ ξhat ℓ := by sorry

end WassDDRO.Reduction
