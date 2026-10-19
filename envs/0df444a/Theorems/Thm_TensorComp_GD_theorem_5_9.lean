-- Prove2me | Theorems.Thm_TensorComp_GD_theorem_5_9
-- name    : TensorComp.GD.theorem_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:44.567536+00:00
-- url     : https://prove2.me/theorems/314b37bb-2082-46cf-a673-2d78f975974a
-- title:
--   Theorem 5.9, p. 23 (L rounded up, r ≥ 2, π a permutation of [r]) — factor retrieval after Gaussian restarts and pruning
-- statement:
--   Under the sampling, noise, rank, restart-count and pruning-threshold conditions (67), Algorithm 3 returns factors $(w^s,\lambda_s)$ that can be matched to the normalized true factors $\bar u^\star_s=u^\star_s/\|u^\star_s\|_2$ by one permutation $\pi$ of the $r$ components. With probability exceeding $1-\delta$, simultaneously for every $s$,
--   $$\|w^s-\bar u^\star_{\pi(s)}\|_2\le K_2E_2,\quad
--     \|w^s-\bar u^\star_{\pi(s)}\|_\infty\le K_\infty E_\infty\sqrt{\mu r/d},\quad
--     |\lambda_s-\lambda^\star_{\pi(s)}|\le K_\lambda E_2\lambda^\star_{\pi(s)}.$$
--   $E_2$ and $E_\infty$ are the complete right-hand-side expressions in (68a) and (68b). This establishes the accuracy of the initialization's individual components.
--
--   **Formalization Note.** The paper prints $\pi:[d]\to[d]$; the factors are indexed by $[r]$, so the formal permutation is of `Fin r`. The real restart count is rounded up, with $r\ge2$ to avoid $\log r=0$. The event requires an admissible pruning output and covers every such output.
-- source:
--   Cai, Li, Poor, Chen, Nonconvex Low-Rank Tensor Completion from Noisy Data, arXiv:1911.04436v2, p. 23, Theorem 5.9, (66)–(68)

import Mathlib
import Definitions.Def_TensorComp_GD_Model

open MeasureTheory

namespace TensorComp.GD

/-- Cai–Li–Poor–Chen, arXiv:1911.04436v2, Theorem 5.9, p. 23.
The paper's `L` is rounded up to a natural number and `r ≥ 2` avoids `log r = 0`. -/
theorem theorem_5_9 :
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c₀ c₁ c₂ c₃ c₄ K₂ Kinf Kweight : ℝ, ∃ d₀ : ℕ,
      0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧
      0 < K₂ ∧ 0 < Kinf ∧ 0 < Kweight ∧ 2 ≤ d₀ ∧
    ∀ (d r : ℕ) (Ustar : Factor d r) (p σ : ℝ)
      {Ωp : Type} [MeasurableSpace Ωp] (P : Measure Ωp)
      [IsProbabilityMeasure P]
      (χ : SortedIdx d → Ωp → Bool)
      (E : SortedIdx d → Ωp → ℝ)
      (g : Fin (Nat.ceil (c₃ * (r : ℝ) ^ (2 * kappa Ustar ^ 2 : ℝ) *
          Real.log r ^ (3 / 2 : ℝ))) → Ωp → EuclideanSpace ℝ (Fin d)),
      d₀ ≤ d → 2 ≤ r →
      (∀ s : Fin r, colNorm Ustar s ≠ 0) →
      0 < p → p ≤ 1 → 0 ≤ σ → Model P p σ χ E g →
      c₀ * mu Ustar ^ 2 * r ^ 4 * Real.log d ^ 4 /
        (d : ℝ) ^ (3 / 2 : ℝ) ≤ p →
      σ / lamMin Ustar ≤
        c₁ * Real.sqrt p /
          ((r : ℝ) ^ (3 / 2 : ℝ) *
           (d : ℝ) ^ (3 / 4 : ℝ) * Real.log d ^ 2) →
      (r : ℝ) ≤ c₂ *
        ((d : ℝ) / (mu Ustar ^ 6 * Real.log d ^ 6)) ^ (1 / 6 : ℝ) →
      let epsTh := c₄ * factorError2 Ustar p σ
      P {ω | ¬ GoodFactors Ustar p σ epsTh K₂ Kinf Kweight χ E g ω} <
        ENNReal.ofReal δ := by sorry

end TensorComp.GD
