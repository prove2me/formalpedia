-- Prove2me | Theorems.Thm_RadGauss_RiskBound_mcdiarmid_step
-- name    : RadGauss.RiskBound.mcdiarmid_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:22:06.330597+00:00
-- url     : https://prove2.me/theorems/0a6f4303-a25f-4c35-96a1-266095ddb02b
-- title:
--   Proof of Theorem 8 — w.p. $\ge 1-\delta/2$, $\sup(\mathbf Eh-\hat{\mathbf E}_nh)\le \mathbf E\sup(\mathbf Eh-\hat{\mathbf E}_nh)+\sqrt{2\ln(2/\delta)/n}$
-- statement:
--   Let $P$ be a probability measure on $\mathcal X \times \mathcal Y$, let $\phi : \mathcal Y \times \mathcal A \to [0, 1]$ be measurable, let $F$ be a class of measurable maps $\mathcal X \to \mathcal A$, let $n \ge 1$ and $0 < \delta < 1$. Let $S = ((X_i, Y_i))_{i=1}^n$ be an i.i.d. sample from $P$. Then with probability at least $1 - \delta/2$,
--
--   $$\sup_{h\in\tilde\phi\circ F}\bigl(\mathbf E h - \hat{\mathbf E}_n h\bigr) \le \mathbf E \sup_{h\in\tilde\phi\circ F}\bigl(\mathbf E h - \hat{\mathbf E}_n h\bigr) + \sqrt{\frac{2\ln(2/\delta)}{n}} .$$
--
--   The outer expectation is over the sample. This is the concentration half of the proof of Theorem 8.
--
--   **Formalization Note** The uniform deviation $S \mapsto \sup_h(\mathbf Eh - \hat{\mathbf E}_nh)$ is assumed measurable (the mission's measurability guard; the paper does not discuss measurability). The statement bounds the measure of the failure event $\{\sup > \mathbf E\sup + \sqrt{2\ln(2/\delta)/n}\}$ by $\delta/2$. The hypothesis $n \ge 1$ is the paper's "integer $n$".
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 467 (PDF p. 5), proof of Theorem 8, last display

import Mathlib
import Definitions.Def_RadGauss_RiskBound_uniformDeviation
import Definitions.Def_RadGauss_RiskBound_phiTildeComp

open MeasureTheory

namespace RadGauss.RiskBound

/-- **Proof of Theorem 8** (p. 467), the McDiarmid step: with probability at least `1 − δ/2` over
an i.i.d. sample of size `n ≥ 1` from `P`,
`sup_{h ∈ φ̃∘F} (E h − Ê_n h) ≤ E sup_{h ∈ φ̃∘F} (E h − Ê_n h) + √(2 ln(2/δ)/n)`.
The uniform deviation is assumed measurable as a function of the sample. -/
theorem mcdiarmid_step {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Zero A]
    (φ : Y → A → ℝ) (hφ : Measurable (Function.uncurry φ))
    (hφ01 : ∀ y a, 0 ≤ φ y a ∧ φ y a ≤ 1)
    (F : Set (X → A)) (hF : ∀ f ∈ F, Measurable f)
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hsup : Measurable (supDev P n (phiTildeComp φ F))) :
    (Measure.pi fun _ : Fin n => P)
      {S | ¬ (supDev P n (phiTildeComp φ F) S ≤
          (∫ S', supDev P n (phiTildeComp φ F) S' ∂(Measure.pi fun _ : Fin n => P)) +
            Real.sqrt (2 * Real.log (2 / δ) / n))}
      ≤ ENNReal.ofReal (δ / 2) := by sorry

end RadGauss.RiskBound
