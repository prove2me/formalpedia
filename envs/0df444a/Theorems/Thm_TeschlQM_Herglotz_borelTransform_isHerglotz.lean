-- Prove2me | Theorems.Thm_TeschlQM_Herglotz_borelTransform_isHerglotz
-- name    : TeschlQM.Herglotz.borelTransform_isHerglotz
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:36:23.7409+00:00
-- url     : https://prove2.me/theorems/a8b5f9fc-8d46-4a3c-aee1-96b44d8f1caa
-- title:
--   Theorem 3.10 — the Borel transform of a finite measure is Herglotz, holomorphic off σ(μ), with |F(z)| ≤ μ(ℝ)/Im z
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb{R}$ with Borel transform $F(z) = \int_{\mathbb{R}} (\lambda - z)^{-1}\, d\mu(\lambda)$ and spectrum $\sigma(\mu)$. Then $F$ is a Herglotz function (when $\mu \neq 0$), $F$ is holomorphic on $\mathbb{C} \setminus \sigma(\mu)$, and
--   $$F(z^*) = F(z)^*, \qquad |F(z)| \le \frac{\mu(\mathbb{R})}{\operatorname{Im}(z)}, \qquad z \in \mathbb{C}_+ .$$
--   This is the easy direction of the correspondence between finite measures and Herglotz functions; Theorem 3.20 is its converse.
--
--   **Formalization Note.** The book states "is a Herglotz function" for every finite measure; for $\mu = 0$ the transform is identically $0$, which does not map $\mathbb{C}_+$ into the open upper half plane, so that conjunct carries the hypothesis $\mu \neq 0$. The other conjuncts are stated for all finite $\mu$. $\mathbb{C} \setminus \sigma(\mu)$ is the set of $z$ different from every real growth point of $\mu$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 99, Theorem 3.10

import Mathlib
import Definitions.Def_TeschlQM_Herglotz_IsHerglotz
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Definitions.Def_TeschlQM_Herglotz_measureSpectrum

open MeasureTheory

namespace TeschlQM.Herglotz

/-- Teschl, p. 99, Theorem 3.10. The Borel transform `F` of a finite Borel measure `μ` on `ℝ` is
a Herglotz function (for `μ ≠ 0`: the transform of the zero measure is `F ≡ 0`, which does not
map `ℂ₊` into the open upper half plane), it is holomorphic on `ℂ \ σ(μ)`, and (3.61)
`F(z*) = F(z)*` and `|F(z)| ≤ μ(ℝ)/Im(z)` for `z ∈ ℂ₊`. -/
theorem borelTransform_isHerglotz (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (μ ≠ 0 → IsHerglotz (borelTransform μ)) ∧
    DifferentiableOn ℂ (borelTransform μ) {z : ℂ | ∀ t ∈ measureSpectrum μ, z ≠ (t : ℂ)} ∧
    ∀ z : ℂ, 0 < z.im →
      borelTransform μ (starRingEnd ℂ z) = starRingEnd ℂ (borelTransform μ z) ∧
      ‖borelTransform μ z‖ ≤ (μ Set.univ).toReal / z.im := by sorry

end TeschlQM.Herglotz
