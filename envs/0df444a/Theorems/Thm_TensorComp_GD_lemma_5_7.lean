-- Prove2me | Theorems.Thm_TensorComp_GD_lemma_5_7
-- name    : TensorComp.GD.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:36.578126+00:00
-- url     : https://prove2.me/theorems/69defdb1-f4c4-4121-985b-c4fb44f5d4ab
-- title:
--   Lemma 5.7, p. 21 — spectral subspace estimate in operator and row norms
-- statement:
--   Let $U$ be any top-$r$ orthonormal eigenspace estimate returned by Algorithm 2, and let $R$ be any orthogonal matrix minimizing $\|UR-U^\star_{\rm orth}\|_F$, where $U^\star_{\rm orth}=U^\star((U^\star)^\top U^\star)^{-1/2}$. Under the lemma's sampling, noise and rank conditions, with failure probability $O(d^{-10})$,
--   $$\|UR-U^\star_{\rm orth}\|\le K_1E_{\rm se},\qquad
--     \|UR-U^\star_{\rm orth}\|_{2,\infty}\le K_2E_{\rm se}\sqrt{\mu r/d}.$$
--   Here $E_{\rm se}$ is exactly the five-term quantity in equation (57), and $K_1,K_2$ are universal comparison constants. This bounds the subspace supplied to factor retrieval.
--
--   **Formalization Note.** The event requires a spectral output and an alignment minimizer to exist; the estimates apply to all such choices. The spectral norm is the Euclidean operator norm.
-- source:
--   Cai, Li, Poor, Chen, Nonconvex Low-Rank Tensor Completion from Noisy Data, arXiv:1911.04436v2, p. 21, Lemma 5.7, (54)–(57)

import Mathlib
import Definitions.Def_TensorComp_GD_Model

open MeasureTheory

namespace TensorComp.GD

/-- Cai–Li–Poor–Chen, arXiv:1911.04436v2, Lemma 5.7, p. 21.
The two comparison constants interpret the paper's `≲` notation. -/
theorem lemma_5_7 :
    ∃ c₀ c₁ c₂ Cf K₁ K₂ : ℝ, ∃ d₀ : ℕ,
      0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < Cf ∧
      0 < K₁ ∧ 0 < K₂ ∧ 2 ≤ d₀ ∧
    ∀ (d r : ℕ) (Ustar : Factor d r) (p σ : ℝ)
      {Ωp : Type} [MeasurableSpace Ωp] (P : Measure Ωp)
      [IsProbabilityMeasure P]
      (χ : SortedIdx d → Ωp → Bool)
      (E : SortedIdx d → Ωp → ℝ),
      d₀ ≤ d → 1 ≤ r →
      (∀ s : Fin r, colNorm Ustar s ≠ 0) →
      0 < p → p ≤ 1 → 0 ≤ σ → ObservationModel P p σ χ E →
      c₀ * mu Ustar ^ 2 * r * Real.log d ^ 2 /
        (d : ℝ) ^ (3 / 2 : ℝ) ≤ p →
      σ / lamMin Ustar ≤
        c₁ * Real.sqrt p /
          ((d : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (Real.log d)) →
      (r : ℝ) ≤ c₂ * Real.sqrt ((d : ℝ) / mu Ustar) →
      P {ω | ¬ GoodSpec Ustar p σ K₁ K₂ χ E ω} ≤
        ENNReal.ofReal (Cf * (d : ℝ) ^ (-(10 : ℝ))) := by sorry

end TensorComp.GD
