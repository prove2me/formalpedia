-- Prove2me | Theorems.Thm_TeschlQM_Herglotz_stieltjes_inversion
-- name    : TeschlQM.Herglotz.stieltjes_inversion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:37:26.382514+00:00
-- url     : https://prove2.me/theorems/341b695e-fcbb-4509-a964-43cad8647efb
-- title:
--   Theorem 3.21 — uniqueness of μ and the Stieltjes inversion formula
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb{R}$ with Borel transform $F$. Then $\mu$ is uniquely determined by $F$: any finite Borel measure $\nu$ whose Borel transform coincides with $F$ on $\mathbb{C}_+$ equals $\mu$. Moreover, for all $\lambda_1 < \lambda_2$ the **Stieltjes inversion formula** holds:
--   $$\frac12\bigl(\mu((\lambda_1, \lambda_2)) + \mu([\lambda_1, \lambda_2])\bigr) = \lim_{\varepsilon \downarrow 0} \frac1\pi \int_{\lambda_1}^{\lambda_2} \operatorname{Im}\bigl(F(\lambda + i\varepsilon)\bigr)\, d\lambda .$$
--   The formula recovers $\mu$ from the boundary behaviour of $\operatorname{Im} F$; atoms at the endpoints are counted with weight $\tfrac12$.
--
--   **Formalization Note.** The book writes the formula for an interval $(\lambda_1, \lambda_2)$ and leaves $\lambda_1 < \lambda_2$ implicit; it is a hypothesis here (at $\lambda_1 = \lambda_2$ the left side is $\tfrac12\mu(\{\lambda_1\})$ while the right side is $0$). The integral is the interval integral `∫ t in l₁..l₂`, the limit is along `𝓝[>] 0`, and the measure values are converted to reals with `toReal` (finite measure).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 108, Theorem 3.21

import Mathlib
import Definitions.Def_TeschlQM_Herglotz_borelTransform

open MeasureTheory Filter
open scoped Topology

namespace TeschlQM.Herglotz

/-- Teschl, p. 108, Theorem 3.21. Let `F` be the Borel transform of a finite Borel measure `μ`.
Then `μ` is unique (any finite Borel measure `ν` whose Borel transform agrees with `F` on `ℂ₊`
equals `μ`) and is recovered by the Stieltjes inversion formula (3.89): for `λ₁ < λ₂`,
`½ (μ((λ₁, λ₂)) + μ([λ₁, λ₂])) = lim_{ε↓0} (1/π) ∫_{λ₁}^{λ₂} Im(F(λ + iε)) dλ`. -/
theorem stieltjes_inversion (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (∀ ν : Measure ℝ, IsFiniteMeasure ν →
      (∀ z : ℂ, 0 < z.im → borelTransform ν z = borelTransform μ z) → ν = μ) ∧
    ∀ l₁ l₂ : ℝ, l₁ < l₂ →
      Tendsto (fun ε : ℝ =>
          (1 / Real.pi) * ∫ t in l₁..l₂, (borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im)
        (𝓝[>] (0 : ℝ))
        (𝓝 (((μ (Set.Ioo l₁ l₂)).toReal + (μ (Set.Icc l₁ l₂)).toReal) / 2)) := by sorry

end TeschlQM.Herglotz
