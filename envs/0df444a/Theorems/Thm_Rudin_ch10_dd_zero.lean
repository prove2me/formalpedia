-- Prove2me | Theorems.Thm_Rudin_ch10_dd_zero
-- name    : Rudin.ch10_dd_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:19:34.906693+00:00
-- url     : https://prove2.me/theorems/b0884580-3a69-42bd-a85c-14d0de2dfa18
-- title:
--   Theorem 10.20 — $d(d\omega) = 0$
-- statement:
--   If $\omega$ is a $k$-form of class $C''$, then $d(d\omega) = 0$: the integral of $d(d\omega)$ over every $(k+2)$-surface is zero.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, p. 261, Theorem 10.20

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 10.20: `d(dω) = 0` for every form `ω` of class `C''`; as forms are
functionals on surfaces, this says that the integral of `d(dω)` over every surface vanishes. -/
theorem ch10_dd_zero (k n : ℕ) (ω : KForm k n) (hω : ∀ i, ContDiff ℝ 2 (ω.coeff i))
    (Φ : SimplexSurface (k + 2) n) (hΦ : ContDiff ℝ 1 Φ.map) :
    integralOverSimplex (extDeriv (extDeriv ω)) Φ = 0 := by sorry

end Rudin
