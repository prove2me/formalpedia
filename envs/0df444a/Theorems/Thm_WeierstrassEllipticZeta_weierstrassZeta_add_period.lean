-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_weierstrassZeta_add_period
-- name    : WeierstrassEllipticZeta.weierstrassZeta_add_period
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-05T01:29:55.252045+00:00
-- url     : https://prove2.me/theorems/a82a9547-ad56-464a-aca0-1454d7cc3b6c
-- title:
--   Quasi-periodicity of the canonical Weierstrass zeta function
-- statement:
--   Let $L$ be any complex period pair, with lattice $\Omega$ and canonical lattice-series zeta function $\zeta_L$. For every $\omega\in\Omega$ and every $z\notin\Omega$,
--
--   $$
--   \zeta_L(z+\omega)=\zeta_L(z)+\eta_L(\omega),
--   \qquad
--   \eta_L(\omega)=\zeta_L(\omega_1/2+\omega)-\zeta_L(\omega_1/2).
--   $$
--
--   Here $\omega_1$ is the first full lattice generator in $L$, so its half lies outside the lattice. The increment is independent of the regular base point. The shift $\omega$ may be any lattice element, including zero; its translate $z+\omega$ is automatically regular.
-- source:
--   NIST DLMF §23.2(iii), equation 23.2.11, https://dlmf.nist.gov/23.2.E11, extended from generators to every lattice element. The constant is normalized by the base-point difference in the mission definition. The proof uses ζ′=−℘ (23.2.7) and periodicity of ℘ (23.2.9).

import Definitions.Def_WeierstrassEllipticZeta_Defs

namespace WeierstrassEllipticZeta

theorem weierstrassZeta_add_period (L : PeriodPair) (ω z : ℂ)
    (hω : ω ∈ L.lattice) (hz : z ∉ L.lattice) :
    weierstrassZeta L (z + ω) = weierstrassZeta L z + zetaQuasiPeriod L ω := by sorry

end WeierstrassEllipticZeta
