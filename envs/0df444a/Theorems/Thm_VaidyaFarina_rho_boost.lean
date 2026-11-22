-- Prove2me | Theorems.Thm_VaidyaFarina_rho_boost
-- name    : VaidyaFarina.rho_boost
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T19:52:19.607214+00:00
-- url     : https://prove2.me/theorems/f6629bc8-ab98-4702-85d5-894f90b55685
-- title:
--   Eq. (15): field-dependent charge-density transformation
-- statement:
--   **Eq. (15): the boosted charge density is field-dependent.** Reading $\rho=(\nabla\cdot E)/4\pi$ and $j=(\nabla\times H-\partial_tE)/4\pi$ as definitions and applying the boost laws $E'=E+v\times H,\ H'=H$, one finds $4\pi(\rho'-\rho+v\cdot j)=-\,v\cdot\partial_tE$, all quantities evaluated at corresponding spacetime points. The right-hand side involves the field $E$, not just the sources: the displacement current in eq. (14) is exactly what makes the source transformation field-dependent.
-- source:
--   A. Vaidya and C. Farina, Phys. Lett. A 153 (1991) 265-267, https://doi.org/10.1016/0375-9601(91)90940-A, p. 266, eq. (15)

import Mathlib
import Definitions.Def_vf_defs

namespace VaidyaFarina
theorem rho_boost(E H : ST → (Fin 3 → ℝ)) (v : Fin 3 → ℝ)
  (hE : ContDiff ℝ 1 E) (hH : ContDiff ℝ 1 H) (p : ST) :
  4 * Real.pi * (rhoOf (boostE v E H) p - rhoOf E (p.1 + p.2 • v, p.2)
      + ∑ i : Fin 3, v i * jOf E H (p.1 + p.2 • v, p.2) i)
    = -∑ i : Fin 3, v i * dT (fun q => E q i) (p.1 + p.2 • v, p.2) := by sorry
end VaidyaFarina
