-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P26_btz_geodesic_turns_before_horizon
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P26.btz_geodesic_turns_before_horizon
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:02:43.131997+00:00
-- url     : https://prove2.me/theorems/8a4a2e66-f1e1-4d11-b0be-21fe1afd8fda
-- title:
--   A finite exterior BTZ geodesic turns before the horizon
-- statement:
--   Let $l,r_+,\rho_0>0$. On a constant Euclidean-time slice of the nonextremal BTZ geometry, use the spatial metric
--
--   $$ds^2=d\rho^2+r_+^2\cosh^2(\rho/l)\,d\phi^2,\qquad \phi\sim\phi+2\pi.$$
--
--   Let $x(t)=(\rho(t),\phi(t))$, $a\le t\le b$ with $a<b$, be an affinely parameterized $C^2$ geodesic, using one fixed angular lift. Suppose $0\le\rho(t)\le\rho_0$, both endpoint radii equal $\rho_0$, and the endpoint angles represent distinct points modulo $2\pi$. Then there is an interior turning point $t_*$ at which
--
--   $$0<\rho(t_*)<\rho_0,\qquad \dot\rho(t_*)=0,\qquad \rho(t_*)\le\rho(t)\quad(a\le t\le b).$$
--
--   Thus this finite exterior geodesic stays away from the horizon. Its geodesic predicate is the Euler–Lagrange equation of the displayed metric’s kinetic energy; it does not assume the turning property.
-- source:
--   Proof of the Holographic Formula for Entanglement Entropy, arXiv:hep-th/0606184v2, PDF p. 9, Section 2, following (2.13)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P26

noncomputable section

open Set

namespace QAlgorithms.Papers.Independent.Intakethird100.P26

/-- PDF p.9, following (2.13) on p.8: a finite nonconstant constant-tau
exterior BTZ geodesic between distinct cutoff-circle endpoints turns strictly
before the horizon. A lift fixes the winding; distinctness is on the actual
angular circle. The permitted radial domain includes the horizon, so strict
positivity of the turning radius is a conclusion. No entropy identity is used. -/
theorem btz_geodesic_turns_before_horizon
    (l rplus rho0 a b : ℝ) (hl : 0 < l) (hrplus : 0 < rplus)
    (hrho0 : 0 < rho0) (hab : a < b)
    (x : ℝ → (Fin 2 → ℝ))
    (hgeo : IsBTZSliceGeodesic l rplus a b x)
    (hcutoff : ∀ t ∈ Icc a b, 0 ≤ x t 0 ∧ x t 0 ≤ rho0)
    (hstart : x a 0 = rho0) (hend : x b 0 = rho0)
    (hdistinct : (↑(x a 1) : AddCircle (2 * Real.pi)) ≠
      (↑(x b 1) : AddCircle (2 * Real.pi))) :
    ∃ t ∈ Ioo a b,
      0 < x t 0 ∧ x t 0 < rho0 ∧ deriv (fun s => x s 0) t = 0 ∧
        ∀ s ∈ Icc a b, x t 0 ≤ x s 0 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P26

end
