-- Prove2me | Theorems.Thm_TensorComp_GD_theorem_2_8
-- name    : TensorComp.GD.theorem_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:25.73724+00:00
-- url     : https://prove2.me/theorems/976e9776-0e6d-4754-8a74-2be19d96b673
-- title:
--   Theorem 2.8, p. 10 (ρ corrected, L rounded up, r ≥ 2) — general-parameter linear convergence of spectrally initialized vanilla GD
-- statement:
--   For a bounded condition number and the explicit sample-size, noise, rank, restart and threshold conditions of Theorem 2.8, spectrally initialized gradient descent obeys the two simultaneous recovery bounds through time $d^5$. With probability at least $1-\delta$, every admissible execution has
--   $$\operatorname{dist}_F(U^t,U^\star)\le\left(C_1\rho^t+C_2\frac\sigma{\lambda^\star_{\min}}\sqrt{\frac{d\log d}{p}}\right)\|U^\star\|_F,$$
--   $$\operatorname{dist}_\infty(U^t,U^\star)\le\operatorname{dist}_{2,\infty}(U^t,U^\star)\le\left(C_3\rho^t+C_4\frac\sigma{\lambda^\star_{\min}}\sqrt{\frac{d\log d}{p}}\right)\|U^\star\|_{2,\infty}.$$
--   This generalizes the bounded-rank, bounded-incoherence goal by showing the paper's explicit parameter dependence.
--
--   **Formalization Note.** The page calls $\rho<1$ an absolute constant for every admissible step size, which is false as $\eta\to0$; the rate is therefore pinned to $\rho=1-(\lambda^\star_{\min})^{4/3}\eta/5$, the range used by Lemmas 5.3–5.6. The restart count $L=c_3r^{2\kappa^2}\log^{3/2}r$ is rounded up to a natural number, and $r\ge2$ is imposed because the printed expression gives $L=0$ at $r=1$. All constants, including a dimension threshold $d_0\ge2$, are chosen after $\delta$ and the bound on $\kappa$ (the paper's $\kappa\asymp1$) and before the instance. Noise has $\psi_2$ norm at most $\sigma$; sampling, noise and Gaussian restarts are jointly independent. The good event asserts existence of an admissible execution before quantifying over all executions; the failure probability is an outer measure.
-- source:
--   Cai, Li, Poor, Chen, Nonconvex Low-Rank Tensor Completion from Noisy Data, arXiv:1911.04436v2, p. 10, Theorem 2.8, (16a)–(16b); pp. 19–20, Lemmas 5.3–5.6

import Mathlib
import Definitions.Def_TensorComp_GD_Model

open MeasureTheory

namespace TensorComp.GD

/-- Cai–Li–Poor–Chen, arXiv:1911.04436v2, Theorem 2.8, p. 10.
The restart count is rounded up and the contraction factor follows Lemmas 5.3–5.6. -/
theorem theorem_2_8 :
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ κbar : ℝ,
    ∃ C₁ C₂ C₃ C₄ c₀ c₁ c₂ c₃ c₄ : ℝ, ∃ d₀ : ℕ,
      0 < C₁ ∧ C₁ < 1 ∧ 0 < C₂ ∧
      0 < C₃ ∧ C₃ < 1 ∧ 0 < C₄ ∧
      0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧ 2 ≤ d₀ ∧
    ∀ (d r : ℕ) (Ustar : Factor d r) (p σ η : ℝ)
      {Ωp : Type} [MeasurableSpace Ωp] (P : Measure Ωp)
      [IsProbabilityMeasure P]
      (χ : SortedIdx d → Ωp → Bool)
      (E : SortedIdx d → Ωp → ℝ)
      (g : Fin (Nat.ceil (c₃ * (r : ℝ) ^ (2 * kappa Ustar ^ 2 : ℝ) *
          Real.log r ^ (3 / 2 : ℝ))) → Ωp → EuclideanSpace ℝ (Fin d)),
      d₀ ≤ d → 2 ≤ r →
      (∀ s : Fin r, colNorm Ustar s ≠ 0) →
      kappa Ustar ≤ κbar →
      0 < p → p ≤ 1 → 0 ≤ σ → Model P p σ χ E g →
      c₀ * mu Ustar ^ 4 * r ^ 4 * Real.log d ^ 4 /
        (d : ℝ) ^ (3 / 2 : ℝ) ≤ p →
      σ / lamMin Ustar ≤
        c₁ * Real.sqrt p /
          (mu Ustar * (r : ℝ) ^ (3 / 2 : ℝ) *
           (d : ℝ) ^ (3 / 4 : ℝ) * Real.log d ^ 2) →
      (r : ℝ) ≤ c₂ *
        ((d : ℝ) / (mu Ustar ^ 6 * Real.log d ^ 6)) ^ (1 / 6 : ℝ) →
      0 < η →
      η ≤ lamMin Ustar ^ (4 / 3 : ℝ) /
        (32 * lamMax Ustar ^ (8 / 3 : ℝ)) →
      let ρ := 1 - lamMin Ustar ^ (4 / 3 : ℝ) * η / 5
      let epsTh := c₄ * factorError2 Ustar p σ
      P {ω | ¬ GoodGD Ustar p σ η epsTh ρ C₁ C₂ C₃ C₄ χ E g ω} ≤
        ENNReal.ofReal δ := by sorry

end TensorComp.GD
