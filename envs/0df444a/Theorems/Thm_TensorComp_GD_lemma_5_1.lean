-- Prove2me | Theorems.Thm_TensorComp_GD_lemma_5_1
-- name    : TensorComp.GD.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:29.538003+00:00
-- url     : https://prove2.me/theorems/9b36ab48-8966-4aea-9fad-03f90c641474
-- title:
--   Lemma 5.1, p. 18 — local strong convexity and smoothness of the clean loss
-- statement:
--   Under the sampling and rank conditions (42), a sufficiently small radius $\delta_r\le c_2/(\mu^{3/2}r)$, and the bounded-condition-number convention used in the proof, the Hessian of the noiseless sampled loss is uniformly bounded on the matrices close to $U^\star$ in both Frobenius and $2,\infty$ norm. Outside an event of probability $O(d^{-10})$, every such $U$ and every direction $V$ satisfy
--   $$\tfrac12(\lambda^\star_{\min})^{4/3}\|V\|_F^2\le D^2f_{\rm clean}(U)[V,V]\le4(\lambda^\star_{\max})^{4/3}\|V\|_F^2.$$
--   This is the paper's local geometry estimate for gradient descent.
--
--   **Formalization Note.** The condition-number upper bound is explicit because the proof invokes it. The failure bound has an existential constant before the instance, and the event is measured by outer measure.
-- source:
--   Cai, Li, Poor, Chen, Nonconvex Low-Rank Tensor Completion from Noisy Data, arXiv:1911.04436v2, p. 18, Lemma 5.1, (42)–(44); p. 33, (109)

import Mathlib
import Definitions.Def_TensorComp_GD_Model

open MeasureTheory

namespace TensorComp.GD

/-- Cai–Li–Poor–Chen, arXiv:1911.04436v2, Lemma 5.1, p. 18.
The proof uses the section's bounded-condition-number convention. -/
theorem lemma_5_1 :
    ∀ κbar : ℝ,
    ∃ c₀ c₁ c₂ Cf : ℝ, ∃ d₀ : ℕ,
      0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < Cf ∧ 2 ≤ d₀ ∧
    ∀ (d r : ℕ) (Ustar : Factor d r) (p δr : ℝ)
      {Ωp : Type} [MeasurableSpace Ωp] (P : Measure Ωp)
      [IsProbabilityMeasure P] (χ : SortedIdx d → Ωp → Bool),
      d₀ ≤ d → 1 ≤ r →
      (∀ s : Fin r, colNorm Ustar s ≠ 0) →
      kappa Ustar ≤ κbar →
      0 < p → p ≤ 1 → SamplingModel P p χ →
      c₀ * max (Real.log d ^ 3 / (d : ℝ) ^ (3 / 2 : ℝ))
        (mu Ustar ^ 2 * r ^ 2 * Real.log d / (d : ℝ) ^ 2) ≤ p →
      (r : ℝ) ≤ c₁ * Real.sqrt ((d : ℝ) / mu Ustar) →
      0 < δr →
      δr ≤ c₂ / (mu Ustar ^ (3 / 2 : ℝ) * r) →
      P {ω | ¬ ∀ U V : Factor d r,
        frobNorm (U - Ustar) ≤ δr * frobNorm Ustar →
        twoInfNorm (U - Ustar) ≤ δr * twoInfNorm Ustar →
        let Ω := omegaOf (fun x => χ x ω)
        let hess := fderiv ℝ
          (fun W : Factor d r =>
            fderiv ℝ (fun Z : Factor d r => cleanLoss p Ω Ustar Z) W V) U V
        (1 / 2 : ℝ) * lamMin Ustar ^ (4 / 3 : ℝ) * frobNorm V ^ 2 ≤ hess ∧
        hess ≤ 4 * lamMax Ustar ^ (4 / 3 : ℝ) * frobNorm V ^ 2} ≤
        ENNReal.ofReal (Cf * (d : ℝ) ^ (-(10 : ℝ))) := by sorry

end TensorComp.GD
