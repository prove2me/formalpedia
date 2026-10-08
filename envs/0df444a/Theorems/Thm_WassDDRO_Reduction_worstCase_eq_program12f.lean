-- Prove2me | Theorems.Thm_WassDDRO_Reduction_worstCase_eq_program12f
-- name    : WassDDRO.Reduction.worstCase_eq_program12f
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:49:02.255832+00:00
-- url     : https://prove2.me/theorems/a3e191d9-eee1-4b75-8b25-1e3829038d02
-- title:
--   Proof of Theorem 4.2, p. 13 — under Assumption 4.1, the optimal values of (10) and (12f) coincide
-- statement:
--   Let $E$, $\Xi$, $\ell=\max_{k\le K}\ell_k$ and samples $\hat\xi_1,\dots,\hat\xi_N\in\Xi$ be as in Theorem 4.2 ($K,N\ge1$, each $\ell_k$ measurable), and suppose Assumption 4.1 holds. Then for every $\varepsilon\ge0$
--   $$\sup_{\mathbb Q\in\mathbb B_\varepsilon(\widehat{\mathbb P}_N)}\mathbb E^{\mathbb Q}[\ell(\xi)]=\left\{\begin{array}{ll}\inf\limits_{\lambda,s_i,z_{ik}}&\lambda\varepsilon+\frac1N\sum_{i=1}^N s_i\\ \text{s.t.}&[-\ell_k+\chi_\Xi]^*(z_{ik})-\langle z_{ik},\hat\xi_i\rangle\le s_i\quad\forall i\le N,\ \forall k\le K\\ &\|z_{ik}\|_*\le\lambda\quad\forall i\le N,\ \forall k\le K.\end{array}\right.$$
--
--   This is the reduction of the infinite-dimensional worst-case expectation problem to the finite convex program (12f); Theorem 4.4 (worst-case distributions) is built on it.
--
--   **Formalization Note** $[-\ell_k+\chi_\Xi]^*(z)$ is encoded as $\sup_{\xi\in\Xi}\big(\langle z,\xi\rangle+\ell_k(\xi)\big)$.
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, proof of Theorem 4.2, p. 13 ("Thus, the optimal values of (10) and (12f) coincide.")

import Mathlib
import Definitions.Def_WassDDRO_Reduction_Setting

open MeasureTheory Filter Topology

namespace WassDDRO.Reduction

/-- Proof of Theorem 4.2, p. 13: under Assumption 4.1, for any `ε ≥ 0` the optimal values of
(10) and (12f) coincide. -/
theorem worstCase_eq_program12f {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ)
    (ε : ℝ) (hε : 0 ≤ ε) (hA : Assumption41 Ξ ℓ) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ) = program12fValue ε Ξ ξhat ℓ := by sorry

end WassDDRO.Reduction
