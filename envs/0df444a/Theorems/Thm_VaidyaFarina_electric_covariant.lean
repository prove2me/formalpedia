-- Prove2me | Theorems.Thm_VaidyaFarina_electric_covariant
-- name    : VaidyaFarina.electric_covariant
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T19:54:18.069194+00:00
-- url     : https://prove2.me/theorems/9fdf05d3-dee3-4fc5-8826-e38be7e9f722
-- title:
--   Eqs. (20)-(22): covariance of the electric Galilean limit
-- statement:
--   **Eqs. (20)–(22): the electric Galilean limit.** With SI-type constants $\varepsilon_0,\mu_0$ and $B=\mu_0H$, the electric limit has field transformations $E'=E$ (20a), $B'=B-\varepsilon_0\mu_0\,v\times E$ (20b) and source transformations $\rho'=\rho$ (21a), $j'=j-\rho v$ (21b). The covariant system is $\nabla\cdot E=\rho/\varepsilon_0,\ \nabla\times E=0,\ \nabla\cdot B=0,\ \nabla\times B=\mu_0j+\varepsilon_0\mu_0\,\partial_tE$ (22): here the $\partial_tH$ term is absent instead of $\partial_tE$. This is the other of the two Le Bellac–Lévy-Leblond Galilean limits.
-- source:
--   A. Vaidya and C. Farina, Phys. Lett. A 153 (1991) 265-267, https://doi.org/10.1016/0375-9601(91)90940-A, p. 267, eqs. (20),(21),(22)

import Mathlib
import Definitions.Def_vf_defs

namespace VaidyaFarina
theorem electric_covariant(e0 mu0 : ℝ) (he0 : e0 ≠ 0) (E B : ST → (Fin 3 → ℝ))
  (rho : ST → ℝ) (j : ST → (Fin 3 → ℝ)) (v : Fin 3 → ℝ)
  (hE : ContDiff ℝ 1 E) (hB : ContDiff ℝ 1 B) (hsys : ElectricSystem e0 mu0 E B rho j) :
  ElectricSystem e0 mu0 (boostEelec v E) (boostBelec e0 mu0 v E B)
    (fun p => rho (p.1 + p.2 • v, p.2))
    (fun p => j (p.1 + p.2 • v, p.2) - rho (p.1 + p.2 • v, p.2) • v) := by sorry
end VaidyaFarina
