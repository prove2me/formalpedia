-- Prove2me | Theorems.Thm_RFRidge_Basic_proposition_2
-- name    : RFRidge.Basic.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:47:55.458802+00:00
-- url     : https://prove2.me/theorems/8ba41f52-259f-4761-a58c-45a8557fcb1c
-- title:
--   Proposition 2 (Bernstein, random vectors), p. 36 — ‖(1/n)Σzᵢ − μ‖ ≤ 2M log(2/δ)/n + √(2σ² log(2/δ)/n) w.p. ≥ 1 − δ
-- statement:
--   Let $z_1,\dots,z_n$ ($n\ge1$) be independent, identically distributed random vectors in a separable Hilbert space $\mathcal H$ with mean $\mu=\mathbb Ez_i$, and let $\sigma,M\ge0$ be such that
--   $$\mathbb E\|z_i-\mu\|_{\mathcal H}^p\le\tfrac12\,p!\,\sigma^2M^{p-2}\qquad\text{for all }p\ge2 .$$
--   Then for every $\delta\in(0,1]$, with probability at least $1-\delta$,
--   $$\Big\|\frac1n\sum_{i=1}^nz_i-\mu\Big\|_{\mathcal H}\le\frac{2M\log\frac2\delta}{n}+\sqrt{\frac{2\sigma^2\log\frac2\delta}{n}} .$$
--
--   This vector Bernstein inequality controls the sample error (Lemma 6) and underlies Proposition 5.
--
--   **Formalization Note** The Hilbert space is real, separable and Borel-measurable; the claim is stated as "the failure event has probability at most $\delta$". The vectors are measurable, mutually independent, identically distributed and Bochner integrable, so $\mu$ exists. The moments $\mathbb E\|z_i-\mu\|^p$ are lower Lebesgue integrals in $[0,\infty]$, so the moment condition also asserts their finiteness. $n\ge1$ is added for $1/n$.
-- source:
--   Rudi & Rosasco, arXiv:1602.04474v5, Proposition 2, p. 36

import Mathlib

namespace RFRidge.Basic

open MeasureTheory ProbabilityTheory

/-- Proposition 2 (Bernstein's inequality for sums of random vectors), p. 36. Let `z₀, …, z_{n−1}` be i.i.d.
random vectors in a real separable Hilbert space `G` with mean `μ = E zᵢ`, and `σ, M ≥ 0` such that
`E‖zᵢ − μ‖^p ≤ ½ p! σ² M^{p−2}` for every `p ≥ 2`. Then for every `δ ∈ (0, 1]`, with probability at
least `1 − δ`, `‖(1/n) Σᵢ zᵢ − μ‖ ≤ 2M log(2/δ)/n + √(2σ² log(2/δ)/n)`; the failure event has
probability at most `δ`. -/
theorem proposition_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    [TopologicalSpace.SeparableSpace G] [MeasurableSpace G] [BorelSpace G]
    (n : ℕ) (hn : 1 ≤ n) (z : Fin n → Ω → G)
    (hmeas : ∀ i, Measurable (z i)) (hind : iIndepFun z P)
    (hid : ∀ i, IdentDistrib (z i) (z ⟨0, hn⟩) P P)
    (hint : ∀ i, Integrable (z i) P) (μ : G) (hμ : ∀ i, μ = ∫ ω, z i ω ∂P)
    (σ M : ℝ) (hσ : 0 ≤ σ) (hM : 0 ≤ M)
    (hmom : ∀ i, ∀ p : ℕ, 2 ≤ p →
      ∫⁻ ω, ENNReal.ofReal (‖z i ω - μ‖ ^ p) ∂P
        ≤ ENNReal.ofReal (1 / 2 * p.factorial * σ ^ 2 * M ^ (p - 2)))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    P {ω | 2 * M * Real.log (2 / δ) / n + Real.sqrt (2 * σ ^ 2 * Real.log (2 / δ) / n)
          < ‖(1 / (n : ℝ)) • ∑ i, z i ω - μ‖} ≤ ENNReal.ofReal δ := by sorry

end RFRidge.Basic
