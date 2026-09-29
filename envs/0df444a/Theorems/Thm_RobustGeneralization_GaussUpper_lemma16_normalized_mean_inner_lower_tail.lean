-- Prove2me | Theorems.Thm_RobustGeneralization_GaussUpper_lemma16_normalized_mean_inner_lower_tail
-- name    : RobustGeneralization.GaussUpper.lemma16_normalized_mean_inner_lower_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:26:06.358876+00:00
-- url     : https://prove2.me/theorems/1872b9e7-b733-450f-a3f9-bbeea73732db
-- title:
--   Lemma 16 — P[⟨ŵ, µ⟩ ≤ (2√n − 1)/(2√n + 4σ)·√d] ≤ 2 exp(−d/(8(σ²+1)))
-- statement:
--   Let $z_1,\dots,z_n\in\mathbb R^d$ be i.i.d. with $z_i\sim\mathcal N_d(\mu,\sigma^2I)$, where $\|\mu\|_2=\sqrt d$ and $\sigma>0$. Let $\bar z=\frac1n\sum_{i=1}^nz_i$ be the sample mean and $\widehat w=\bar z/\|\bar z\|_2$ the unit vector in its direction. Then
--
--   $$\mathbb P\left[\langle\widehat w,\mu\rangle\le\frac{2\sqrt n-1}{2\sqrt n+4\sigma}\sqrt d\right]\le2\exp\left(-\frac{d}{8(\sigma^2+1)}\right).$$
--
--   Since $\|\mu\|_2=\sqrt d$, the ratio $\langle\widehat w,\mu\rangle/\sqrt d$ is the cosine of the angle between the estimate and the truth; the lemma shows it is at least $(2\sqrt n-1)/(2\sqrt n+4\sigma)$ with high probability. This is the statement on which Theorems 18 and 21 rest.
--
--   **Formalization Note** $\widehat w$ is $\|\bar z\|_2^{-1}\bar z$, which equals $0$ on the null event $\bar z=0$. No hypothesis on $n$ is needed: at $n=0$, $\bar z=0$ and the event reads $0\le-\sqrt d/(4\sigma)$, which is empty unless $d=0$, where the bound is $2$.
-- source:
--   Schmidt et al., Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 23, Lemma 16

import Mathlib
import Definitions.Def_RobustGeneralization_GaussUpper_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussUpper

/-- **Lemma 16** (p. 23). For `z₁, …, zₙ` i.i.d. `N_d(µ, σ² I)` with `‖µ‖₂ = √d` and `σ > 0`, and
`ŵ = z̄/‖z̄‖₂`, `P[⟨ŵ, µ⟩ ≤ (2√n - 1)/(2√n + 4σ) · √d] ≤ 2 exp(-d/(8(σ² + 1)))`. -/
theorem lemma16_normalized_mean_inner_lower_tail (d n : ℕ) (μ : E d) (hμ : ‖μ‖ = Real.sqrt d)
    (σ : ℝ) (hσ : 0 < σ) :
    (Measure.pi fun _ : Fin n => gaussVec μ σ)
        {z | inner ℝ (what' z) μ ≤
          (2 * Real.sqrt n - 1) / (2 * Real.sqrt n + 4 * σ) * Real.sqrt d} ≤
      ENNReal.ofReal (2 * Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1)))) := by sorry

end RobustGeneralization.GaussUpper
