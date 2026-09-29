-- Prove2me | Theorems.Thm_Weinberg1965_photonIndex_closed_form
-- name    : Weinberg1965.photonIndex_closed_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:55:01.439989+00:00
-- url     : https://prove2.me/theorems/5b1b3c65-1fae-40f3-b5ed-ca6cbf60991a
-- title:
--   Eq. (2.16) — closed form of the infrared-photon exponent $A$
-- statement:
--   Let the external lines $n$ have masses $m_n>0$, three-momenta $\mathbf p_n$, charges $e_n$ and signs $\eta_n=\pm1$, and let $\beta_{nm}$ be the relative velocity (2.17). Then the solid-angle integral (2.14) of the photon angular function (2.15) is
--   $$A=-\frac{1}{8\pi^2}\sum_{n,m}\eta_n\eta_me_ne_m\,\beta_{nm}^{-1}\ln\Bigl(\frac{1+\beta_{nm}}{1-\beta_{nm}}\Bigr),$$
--   where the pair kernel $\beta^{-1}\ln\frac{1+\beta}{1-\beta}$ is given its limiting value $2$ when $\beta_{nm}=0$ (in particular for the diagonal terms $n=m$).
--
--   This is the elementary integral (2.16) that turns the infrared-photon exponent into an explicit function of the external momenta; it fixes the power $(\lambda/\Lambda)^A$ in (2.18) and $E^A$ in the soft-photon spectrum (2.51).
-- source:
--   S. Weinberg, Infrared Photons and Gravitons, Phys. Rev. 140, B516 (1965), https://doi.org/10.1103/PhysRev.140.B516, p. B518, Sec. II.3, Eqs. (2.14)–(2.17)

import Definitions.Def_Weinberg1965_Defs

namespace Weinberg1965

theorem photonIndex_closed_form {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (p : ι → Vec3) (e η : ι → ℝ)
    (hm : ∀ n, 0 < m n) (hη : ∀ n, η n = 1 ∨ η n = -1) :
    photonIndex m p e η =
      -(1 / (8 * Real.pi ^ 2)) *
        ∑ n, ∑ k, η n * η k * e n * e k * photonKernel (relVel (m n) (p n) (m k) (p k)) := by
  sorry

end Weinberg1965
