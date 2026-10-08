-- Prove2me | Theorems.Thm_WassDDRO_Reduction_worstCase_eq_sampleAverage_of_zero
-- name    : WassDDRO.Reduction.worstCase_eq_sampleAverage_of_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:44:47.202875+00:00
-- url     : https://prove2.me/theorems/fdf769f4-910c-4530-a214-93b562f8c4b5
-- title:
--   Proof of Theorem 4.2, p. 13 — the case ε = 0: (10) is the sample average and (12b) tends to it as λ → ∞
-- statement:
--   Let $E$, $\Xi$, $\ell=\max_{k\le K}\ell_k$ and samples $\hat\xi_1,\dots,\hat\xi_N\in\Xi$ be as in Theorem 4.2 ($K,N\ge1$, each $\ell_k$ measurable), and suppose Assumption 4.1 holds. Then:
--
--   1. with radius $\varepsilon=0$, the worst-case expectation (10) equals the sample average,
--   $$\sup_{\mathbb Q\in\mathbb B_0(\widehat{\mathbb P}_N)}\mathbb E^{\mathbb Q}[\ell(\xi)]=\frac1N\sum_{i=1}^N\ell(\hat\xi_i);$$
--   2. the objective of (12b) at $\varepsilon=0$ converges to the sample average as $\lambda\to\infty$:
--   $$\lim_{\lambda\to\infty}\frac1N\sum_{i=1}^N\sup_{\xi\in\Xi}\big(\ell(\xi)-\lambda\|\xi-\hat\xi_i\|\big)=\frac1N\sum_{i=1}^N\ell(\hat\xi_i);$$
--   3. consequently (12a) holds with equality also at $\varepsilon=0$: (10) with $\varepsilon=0$ equals the optimal value of (12c) with $\varepsilon=0$.
--
--   Together with the case $\varepsilon>0$ this shows that (10) equals (12c) for all $\varepsilon\ge0$.
--
--   **Formalization Note** The sums are taken in `EReal`. Under Assumption 4.1 no $\ell_k$ takes the value $+\infty$, so each $\ell(\hat\xi_i)<+\infty$, and for $\lambda$ large enough each inner supremum is $<+\infty$; the sums therefore never meet $(+\infty)+(-\infty)$ where it matters, and a sample with $\ell(\hat\xi_i)=-\infty$ makes the average $-\infty$, as in the paper. The limit is in the order topology of $\overline{\mathbb R}$.
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, proof of Theorem 4.2, p. 13 (the case ε = 0)

import Mathlib
import Definitions.Def_WassDDRO_Reduction_Setting

open MeasureTheory Filter Topology

namespace WassDDRO.Reduction

/-- Proof of Theorem 4.2, p. 13 (the case `ε = 0`): under Assumption 4.1, (10) with
`ε = 0` is the sample average `(1/N) Σ ℓ(ξ̂ᵢ)`, the objective of (12b) at `ε = 0` converges
to that sample average as `λ → ∞`, and (12a) holds with equality at `ε = 0`. -/
theorem worstCase_eq_sampleAverage_of_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ)
    (hA : Assumption41 Ξ ℓ) :
    worstCaseExpectation 0 Ξ ξhat (maxLoss ℓ)
        = ((1 / (N : ℝ) : ℝ) : EReal) * (∑ i, maxLoss ℓ (ξhat i)) ∧
      Tendsto (fun lam : ℝ => ((1 / (N : ℝ) : ℝ) : EReal) *
          ∑ i, (⨆ ξ ∈ Ξ, maxLoss ℓ ξ - ((lam * ‖ξ - ξhat i‖ : ℝ) : EReal)))
        atTop (𝓝 (((1 / (N : ℝ) : ℝ) : EReal) * (∑ i, maxLoss ℓ (ξhat i)))) ∧
      worstCaseExpectation 0 Ξ ξhat (maxLoss ℓ) = program12cValue 0 Ξ ξhat (maxLoss ℓ) := by sorry

end WassDDRO.Reduction
