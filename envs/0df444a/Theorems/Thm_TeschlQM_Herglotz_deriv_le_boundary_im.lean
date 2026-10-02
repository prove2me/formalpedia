-- Prove2me | Theorems.Thm_TeschlQM_Herglotz_deriv_le_boundary_im
-- name    : TeschlQM.Herglotz.deriv_le_boundary_im
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:38:07.755714+00:00
-- url     : https://prove2.me/theorems/4b24d71c-a137-4079-86d3-c250d7117ebc
-- title:
--   Theorem 3.22 — D̲μ ≤ liminf (1/π) Im F(λ+iε) ≤ limsup (1/π) Im F(λ+iε) ≤ D̄μ
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb{R}$ with Borel transform $F$, and let $\underline{D}\mu$, $\overline{D}\mu$ be its lower and upper derivatives with respect to Lebesgue measure. Then for every $\lambda \in \mathbb{R}$
--   $$(\underline{D}\mu)(\lambda) \le \liminf_{\varepsilon\downarrow 0} \frac1\pi \operatorname{Im} F(\lambda + i\varepsilon) \le \limsup_{\varepsilon\downarrow 0} \frac1\pi \operatorname{Im} F(\lambda + i\varepsilon) \le (\overline{D}\mu)(\lambda).$$
--   So the boundary values of $\operatorname{Im} F$ are squeezed between the lower and upper derivatives of $\mu$, which is how the Radon–Nikodym derivative of $\mu$ is read off from $F$.
--
--   **Formalization Note.** The printed (3.90) has $\frac1\pi F(\lambda + i\varepsilon)$ without $\operatorname{Im}$, a complex number that cannot be compared with the real derivatives; the proof on the same page estimates $\operatorname{Im}(F(\lambda + i\varepsilon))$, and that is what is stated. Since $\operatorname{Im} F(\lambda + i\varepsilon) = \int \varepsilon/((t-\lambda)^2+\varepsilon^2)\,d\mu(t) \ge 0$ for $\varepsilon > 0$, the quantities are compared in $[0,\infty]$ via `ENNReal.ofReal`, which loses nothing on nonnegative reals.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 108, Theorem 3.22

import Mathlib
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Definitions.Def_TeschlQM_Herglotz_lowerDeriv
import Definitions.Def_TeschlQM_Herglotz_upperDeriv

open MeasureTheory Filter
open scoped ENNReal Topology

namespace TeschlQM.Herglotz

/-- Teschl, p. 108, Theorem 3.22. Let `μ` be a finite Borel measure and `F` its Borel transform.
Then, for every `λ ∈ ℝ`, (3.90)
`(D̲μ)(λ) ≤ liminf_{ε↓0} (1/π) Im F(λ + iε) ≤ limsup_{ε↓0} (1/π) Im F(λ + iε) ≤ (D̄μ)(λ)`.
The printed (3.90) omits `Im`; the proof on pp. 108–109 estimates `Im(F(λ + iε))`, which is
nonnegative for `ε > 0`, so the quantities are compared in `[0, ∞]`. -/
theorem deriv_le_boundary_im (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    lowerDeriv μ t ≤ liminf (fun ε : ℝ => ENNReal.ofReal
        ((borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) ∧
    liminf (fun ε : ℝ => ENNReal.ofReal
        ((borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) ≤
      limsup (fun ε : ℝ => ENNReal.ofReal
        ((borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) ∧
    limsup (fun ε : ℝ => ENNReal.ofReal
        ((borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) ≤
      upperDeriv μ t := by sorry

end TeschlQM.Herglotz
