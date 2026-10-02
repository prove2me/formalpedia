-- Prove2me | Theorems.Thm_TeschlQM_Herglotz_boundary_im_eq_deriv
-- name    : TeschlQM.Herglotz.boundary_im_eq_deriv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:38:46.86602+00:00
-- url     : https://prove2.me/theorems/8199c8f0-b43a-40b9-ac8d-7608bcc80e8e
-- title:
--   Theorem 3.23 — (1/π) Im F(λ+iε) → (Dμ)(λ) a.e.; supports of μ_sc and minimal support of μ_ac
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb{R}$ with Borel transform $F$. Then the limit
--   $$\operatorname{Im}(F(\lambda)) = \lim_{\varepsilon\downarrow 0} \frac1\pi \operatorname{Im}\bigl(F(\lambda + i\varepsilon)\bigr) \in [0, \infty]$$
--   exists (finite or infinite) for $\mu$-almost every and for Lebesgue-almost every $\lambda$, and it equals the derivative $(D\mu)(\lambda)$ at every $\lambda$ where $(D\mu)(\lambda)$ exists. Moreover, the set $\{\lambda \mid \operatorname{Im}(F(\lambda)) = \infty\}$ is a support for the singularly continuous part $\mu_{sc}$, and $\{\lambda \mid 0 < \operatorname{Im}(F(\lambda)) < \infty\}$ is a minimal support for the absolutely continuous part $\mu_{ac}$.
--
--   These are the boundary-value characterizations of the spectral types used later for Schrödinger operators.
--
--   **Formalization Note.** The book's (3.91) defines $\operatorname{Im}(F(\lambda))$ with the factor $\frac1\pi$ and (3.92) then writes $(D\mu)(\lambda) = \frac1\pi\operatorname{Im}(F(\lambda))$, which would apply the factor twice; consistent with Theorem 3.22 the identity is stated as $(D\mu)(\lambda) = \lim_{\varepsilon\downarrow0}\frac1\pi\operatorname{Im}F(\lambda+i\varepsilon)$. Limits are taken in `ℝ≥0∞` along `𝓝[>] 0`; the two support sets are defined through these limits (the set where the limit exists and is $\infty$, resp. exists and lies in $(0,\infty)$), so no value is assigned where the limit fails to exist.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 109, Theorem 3.23

import Mathlib
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Definitions.Def_TeschlQM_Herglotz_HasMeasureDeriv
import Definitions.Def_TeschlQM_Herglotz_IsSupport
import Definitions.Def_TeschlQM_Herglotz_IsMinimalSupport
import Definitions.Def_TeschlQM_Herglotz_acPart
import Definitions.Def_TeschlQM_Herglotz_scPart

open MeasureTheory Filter
open scoped ENNReal Topology

namespace TeschlQM.Herglotz

/-- Teschl, p. 109, Theorem 3.23. Let `μ` be a finite Borel measure and `F` its Borel transform.
The limit (3.91) `Im(F(λ)) = lim_{ε↓0} (1/π) Im(F(λ + iε))` exists in `[0, ∞]` (finite or
infinite) for `μ`-a.e. and for Lebesgue-a.e. `λ`; it equals `(Dμ)(λ)` whenever `(Dμ)(λ)` exists
((3.92), read with the factor `1/π` taken once, consistent with Theorem 3.22); the set where it
is `∞` is a support for the singularly continuous part `μ_sc`, and the set where it lies in
`(0, ∞)` is a minimal support for the absolutely continuous part `μ_ac`. -/
theorem boundary_im_eq_deriv (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (∀ᵐ (t : ℝ) ∂μ, ∃ L : ℝ≥0∞, Tendsto (fun ε : ℝ => ENNReal.ofReal
        ((borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) (𝓝 L)) ∧
    (∀ᵐ (t : ℝ) ∂(volume : Measure ℝ), ∃ L : ℝ≥0∞, Tendsto (fun ε : ℝ => ENNReal.ofReal
        ((borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) (𝓝 L)) ∧
    (∀ (t : ℝ) (d : ℝ≥0∞), HasMeasureDeriv μ t d →
      Tendsto (fun ε : ℝ => ENNReal.ofReal
        ((borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) (𝓝 d)) ∧
    IsSupport (scPart μ) {t : ℝ | Tendsto (fun ε : ℝ => ENNReal.ofReal
        ((borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) (𝓝 ⊤)} ∧
    IsMinimalSupport (acPart μ) {t : ℝ | ∃ L : ℝ≥0∞, 0 < L ∧ L < ⊤ ∧
      Tendsto (fun ε : ℝ => ENNReal.ofReal
        ((borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) (𝓝 L)} := by sorry

end TeschlQM.Herglotz
