-- Prove2me | Theorems.Thm_Rudin_ch10_pullback_extDeriv
-- name    : Rudin.ch10_pullback_extDeriv
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:21:29.970497+00:00
-- url     : https://prove2.me/theorems/af7d592a-2efe-4e83-a0f2-ca321c814b29
-- title:
--   Theorem 10.22(c) — pullback commutes with $d$
-- statement:
--   For a $C''$-mapping $T$ and a $k$-form $\omega$ of class $C'$, $(d\omega)_T = d(\omega_T)$, as an identity of forms.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, p. 263, Theorem 10.22(c)

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 10.22(c): pullback commutes with exterior differentiation,
`(dω)_T = d(ω_T)`, an identity of forms, i.e. of their integrals over all surfaces. -/
theorem ch10_pullback_extDeriv (k m n : ℕ) (T : (Fin m → ℝ) → (Fin n → ℝ))
    (hT : ContDiff ℝ 2 T) (ω : KForm k n) (hω : ∀ i, ContDiff ℝ 1 (ω.coeff i))
    (Φ : SimplexSurface (k + 1) m) (hΦ : ContDiff ℝ 1 Φ.map) :
    integralOverSimplex (pullback T (extDeriv ω)) Φ =
      integralOverSimplex (extDeriv (pullback T ω)) Φ := by sorry

end Rudin
