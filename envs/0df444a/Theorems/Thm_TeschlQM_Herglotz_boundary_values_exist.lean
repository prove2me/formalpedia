-- Prove2me | Theorems.Thm_TeschlQM_Herglotz_boundary_values_exist
-- name    : TeschlQM.Herglotz.boundary_values_exist
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:39:52.839983+00:00
-- url     : https://prove2.me/theorems/878474f4-0a98-4946-b387-325b27810b2f
-- title:
--   Corollary 3.25 — lim F(λ+iε) exists μ-a.e. and Lebesgue-a.e., and is finite Lebesgue-a.e.
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb{R}$ with Borel transform $F$. Then the limit
--   $$\lim_{\varepsilon\downarrow 0} F(\lambda + i\varepsilon)$$
--   exists, either as a complex number or as $\infty$, for $\mu$-almost every and for Lebesgue-almost every $\lambda$, and it is finite for Lebesgue-almost every $\lambda$.
--
--   **Formalization Note.** "Exists" includes the value $\infty$ (the book's proof: $\operatorname{Im} F(\lambda+i\varepsilon) \to \infty$ implies $F(\lambda+i\varepsilon) \to \infty$); the limit $\infty$ is `Tendsto … (Bornology.cobounded ℂ)`, i.e. $|F(\lambda + i\varepsilon)| \to \infty$. Limits are along `𝓝[>] 0`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 110, Corollary 3.25

import Mathlib
import Definitions.Def_TeschlQM_Herglotz_borelTransform

open MeasureTheory Filter
open scoped Topology

namespace TeschlQM.Herglotz

/-- Teschl, p. 110, Corollary 3.25. Let `μ` be a finite Borel measure and `F` its Borel
transform. The limit (3.93) `lim_{ε↓0} F(λ + iε)` exists, as a complex number or as `∞`
(`|F(λ + iε)| → ∞`), for `μ`-a.e. and for Lebesgue-a.e. `λ`, and it is finite for Lebesgue-a.e.
`λ`. -/
theorem boundary_values_exist (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (∀ᵐ (t : ℝ) ∂μ,
      (∃ L : ℂ, Tendsto (fun ε : ℝ => borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 L)) ∨
      Tendsto (fun ε : ℝ => borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I))
        (𝓝[>] (0 : ℝ)) (Bornology.cobounded ℂ)) ∧
    (∀ᵐ (t : ℝ) ∂(volume : Measure ℝ),
      (∃ L : ℂ, Tendsto (fun ε : ℝ => borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 L)) ∨
      Tendsto (fun ε : ℝ => borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I))
        (𝓝[>] (0 : ℝ)) (Bornology.cobounded ℂ)) ∧
    (∀ᵐ (t : ℝ) ∂(volume : Measure ℝ), ∃ L : ℂ,
      Tendsto (fun ε : ℝ => borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 L)) := by sorry

end TeschlQM.Herglotz
