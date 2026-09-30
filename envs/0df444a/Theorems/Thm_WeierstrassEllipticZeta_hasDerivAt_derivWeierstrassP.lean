-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_derivWeierstrassP
-- name    : WeierstrassEllipticZeta.hasDerivAt_derivWeierstrassP
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-05T00:47:52.405283+00:00
-- url     : https://prove2.me/theorems/2f84b41d-4570-4066-b8b8-a3aa2408b87d
-- title:
--   The second-order differential equation for the Weierstrass function
-- statement:
--   Let $L$ be any complex period pair, with lattice $\Omega$ and associated Weierstrass function $\wp$. At every $z\in\mathbb C\setminus\Omega$, the complex derivative of $\wp'$ exists and satisfies
--
--   $$
--   \wp''(z)=6\wp(z)^2-\frac{g_2}{2}.
--   $$
--
--   There is no hypothesis that $\wp'(z)$ is nonzero. This includes the regular critical points. The functions and invariant are the canonical Mathlib lattice-series definitions, with no additional arithmetic assumptions on the lattice.
-- source:
--   NIST DLMF §23.3(ii), equation 23.3.12, https://dlmf.nist.gov/23.3.E12. Differentiate the cubic equation 23.3.10, https://dlmf.nist.gov/23.3.E10, and extend over the isolated zeros of ℘′. The underlying cubic identity is Mathlib PeriodPair.derivWeierstrassP_sq.

import Definitions.Def_WeierstrassEllipticZeta_Defs

namespace WeierstrassEllipticZeta

theorem hasDerivAt_derivWeierstrassP (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    HasDerivAt L.derivWeierstrassP (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) z := by sorry

end WeierstrassEllipticZeta
