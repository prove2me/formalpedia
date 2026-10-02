-- Prove2me | Theorems.Thm_RobustGeneralization_GaussUpper_lemma14_sample_mean_norm_tail_sqrt_d
-- name    : RobustGeneralization.GaussUpper.lemma14_sample_mean_norm_tail_sqrt_d
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:24:53.281627+00:00
-- url     : https://prove2.me/theorems/ff059819-72cb-450a-a181-3e1081352fbe
-- title:
--   Lemma 14 — for ‖µ‖₂ = √d: P[‖z̄‖₂ ≥ (1 + 2σ/√n)√d] ≤ e^{−d/2}
-- statement:
--   Let $z_1,\dots,z_n\in\mathbb R^d$ be i.i.d. with $z_i\sim\mathcal N_d(\mu,\sigma^2I)$, where $\|\mu\|_2=\sqrt d$ and $\sigma>0$, and let $\bar z=\frac1n\sum_{i=1}^nz_i$. Then
--
--   $$\mathbb P\left[\|\bar z\|_2\ge\Big(1+\frac{2\sigma}{\sqrt n}\Big)\sqrt d\right]\le e^{-d/2}.$$
--
--   This is Lemma 13 instantiated in the regime of the Gaussian model, where the mean has norm $\sqrt d$ and the failure probability is exponentially small in $d$.
--
--   **Formalization Note** No hypothesis on $n$ is needed: at $n=0$, Lean's conventions give $\bar z=0$ and $2\sigma/\sqrt0=0$, so the event is $\sqrt d\le0$, which is empty unless $d=0$, where the bound is $e^0=1$.
-- source:
--   Schmidt et al., Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 23, Lemma 14

import Mathlib
import Definitions.Def_RobustGeneralization_GaussUpper_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussUpper

/-- **Lemma 14** (p. 23). For `z₁, …, zₙ` i.i.d. `N_d(µ, σ² I)` with `‖µ‖₂ = √d` and `σ > 0`, the
sample mean satisfies `P[‖z̄‖₂ ≥ (1 + 2σ/√n)√d] ≤ exp(-d/2)`. -/
theorem lemma14_sample_mean_norm_tail_sqrt_d (d n : ℕ) (μ : E d) (hμ : ‖μ‖ = Real.sqrt d)
    (σ : ℝ) (hσ : 0 < σ) :
    (Measure.pi fun _ : Fin n => gaussVec μ σ)
        {z | (1 + 2 * σ / Real.sqrt n) * Real.sqrt d ≤ ‖zbar' z‖} ≤
      ENNReal.ofReal (Real.exp (-(d : ℝ) / 2)) := by sorry

end RobustGeneralization.GaussUpper
