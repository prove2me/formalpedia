-- Prove2me | Theorems.Thm_Rudin_ch10_pullback_integral
-- name    : Rudin.ch10_pullback_integral
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:24:57.601559+00:00
-- url     : https://prove2.me/theorems/9563c2ab-353f-4026-ba7d-4e135b5981ab
-- title:
--   Theorem 10.25 — integration and pullback
-- statement:
--   If $\Phi$ is a $k$-surface in $\mathbb{R}^m$ and $T$ is a $C'$-mapping into $\mathbb{R}^n$, then $\int_{T\circ\Phi}\omega = \int_\Phi \omega_T$ for every $k$-form $\omega$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, p. 265, Theorem 10.25

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 10.25: integrating a form over the image surface `T ∘ Φ` is the same as
integrating its pullback over `Φ`. -/
theorem ch10_pullback_integral (k m n : ℕ) (T : (Fin m → ℝ) → (Fin n → ℝ))
    (hT : ContDiff ℝ 1 T) (ω : KForm k n) (Φ : SimplexSurface k m) (hΦ : ContDiff ℝ 1 Φ.map) :
    integralOverSimplex ω ⟨T ∘ Φ.map⟩ = integralOverSimplex (pullback T ω) Φ := by sorry

end Rudin
