-- Prove2me | Theorems.Thm_VaidyaFarina_homogeneous_covariant
-- name    : VaidyaFarina.homogeneous_covariant
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T19:51:52.543094+00:00
-- url     : https://prove2.me/theorems/0c001c12-51b9-4ff6-a3c3-2378df2e5325
-- title:
--   Galilean covariance of the homogeneous Maxwell equations
-- statement:
--   **Galilean covariance of the homogeneous Maxwell equations (eqs. (5),(6)).** If $(E,H)$ satisfy $\nabla\cdot H=0$ and $\partial_tH=-\nabla\times E$, then so do the boosted fields $H'=H,\ E'=E+v\times H$ (with the coordinate change $x'=x-vt,\ t'=t$). Vaidya–Farina note (p. 266) that this covariance is "an accidental mathematical result": it holds for the homogeneous pair even though the transformation laws are Galilean, not Lorentzian.
-- source:
--   A. Vaidya and C. Farina, Phys. Lett. A 153 (1991) 265-267, https://doi.org/10.1016/0375-9601(91)90940-A, p. 266, covariance of eqs. (5),(6)

import Mathlib
import Definitions.Def_vf_defs

namespace VaidyaFarina
theorem homogeneous_covariant(E H : ST → (Fin 3 → ℝ)) (v : Fin 3 → ℝ)
  (hE : ContDiff ℝ 1 E) (hH : ContDiff ℝ 1 H)
  (hdiv : ∀ p, vdiv H p = 0) (hfar : ∀ p, vdt H p = -curl E p) :
  (∀ p, vdiv (boostH v H) p = 0) ∧ (∀ p, vdt (boostH v H) p = -curl (boostE v E H) p) := by sorry
end VaidyaFarina
