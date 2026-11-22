-- Prove2me | Theorems.Thm_VaidyaFarina_magnetic_covariant
-- name    : VaidyaFarina.magnetic_covariant
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T19:53:13.753049+00:00
-- url     : https://prove2.me/theorems/62d368e6-109f-46d0-b53f-26afefd50bee
-- title:
--   Eqs. (17)-(19): covariance of the modified (magnetic-limit) system
-- statement:
--   **Eqs. (17)–(19): the modified (magnetic-limit) system is Galilean covariant.** If the displacement current is dropped, so the current is defined by $4\pi j=\nabla\times H$ (eq. (17)), then the resulting system is Galilean covariant with the field-independent source laws $\rho'=\rho-v\cdot j$ (eq. (18)) and $j'=j$ (eq. (19)). This is the consistent theory one is forced to adopt if sources must transform as matter — but it is no longer the full Maxwell system.
-- source:
--   A. Vaidya and C. Farina, Phys. Lett. A 153 (1991) 265-267, https://doi.org/10.1016/0375-9601(91)90940-A, p. 266, eqs. (17),(18),(19)

import Mathlib
import Definitions.Def_vf_defs

namespace VaidyaFarina
theorem magnetic_covariant(E H : ST → (Fin 3 → ℝ)) (rho : ST → ℝ) (j : ST → (Fin 3 → ℝ)) (v : Fin 3 → ℝ)
  (hE : ContDiff ℝ 1 E) (hH : ContDiff ℝ 1 H) (hsys : MagneticSystem E H rho j) :
  MagneticSystem (boostE v E H) (boostH v H)
    (fun p => rho (p.1 + p.2 • v, p.2) - ∑ i : Fin 3, v i * j (p.1 + p.2 • v, p.2) i)
    (fun p => j (p.1 + p.2 • v, p.2)) := by sorry
end VaidyaFarina
