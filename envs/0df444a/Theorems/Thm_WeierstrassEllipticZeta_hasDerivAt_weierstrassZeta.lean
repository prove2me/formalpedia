-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
-- name    : WeierstrassEllipticZeta.hasDerivAt_weierstrassZeta
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-05T00:00:15.406952+00:00
-- url     : https://prove2.me/theorems/9d009034-3d4c-416b-90eb-35a15f91a612
-- title:
--   The canonical Weierstrass zeta function has derivative −℘
-- statement:
--   Let $L$ be a complex period pair, let $\Omega$ be its lattice, and let $\zeta_L$ be the canonical lattice-series zeta function. At every $z\notin\Omega$, its complex derivative exists and satisfies
--   $$\zeta_L'(z)=-\wp_L(z).$$
--   Both functions are the fixed constructions used by the mission. This is a derivative statement, so it also establishes continuity at every regular point, as needed when extending the addition identity across coincident $\wp$ values.
-- source:
--   NIST DLMF §23.2(ii), equations 23.2.5 and 23.2.7, https://dlmf.nist.gov/23.2.E7.

import Definitions.Def_WeierstrassEllipticZeta_Defs

namespace WeierstrassEllipticZeta

theorem hasDerivAt_weierstrassZeta (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z := by sorry

end WeierstrassEllipticZeta
