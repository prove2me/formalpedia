-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_nondegenerate
-- name    : WeierstrassEllipticZeta.zeta_addition_nondegenerate
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-05T00:00:16.236617+00:00
-- url     : https://prove2.me/theorems/1aedb110-be9f-4b72-a6f8-cc6155618d26
-- title:
--   Zeta addition formula for distinct ℘ values
-- statement:
--   Let $L$ be a complex period pair with lattice $\Omega$, and suppose $z,v,z+v\notin\Omega$ and $\wp_L(v)\ne\wp_L(z)$. Then the canonical lattice-series zeta function satisfies
--   $$\zeta_L(z+v)=\zeta_L(z)+\zeta_L(v)+\frac{\wp_L'(v)-\wp_L'(z)}{2(\wp_L(v)-\wp_L(z))}.$$
--   This is the classical divided addition formula. It is the remaining analytic child of the first mission milestone: a separate continuity reduction extends it to the required multiplied-out formula without imposing distinct $\wp$ values on the milestone.
-- source:
--   NIST DLMF §23.10(i), equation 23.10.2, https://dlmf.nist.gov/23.10.E2, using ζ′=−℘ from 23.2.7; equivalently Senthil Kumar K (2026), §4, equation (5), https://doi.org/10.1017/S001309152610145X, after division when ℘(v)≠℘(z).

import Definitions.Def_WeierstrassEllipticZeta_Defs

namespace WeierstrassEllipticZeta

theorem zeta_addition_nondegenerate (L : PeriodPair) (z v : ℂ)
    (hz : z ∉ L.lattice) (hv : v ∉ L.lattice) (hzv : z + v ∉ L.lattice)
    (hdelta : L.weierstrassP v ≠ L.weierstrassP z) :
    weierstrassZeta L (z + v) = weierstrassZeta L z + weierstrassZeta L v +
      (L.derivWeierstrassP v - L.derivWeierstrassP z) /
        (2 * (L.weierstrassP v - L.weierstrassP z)) := by sorry

end WeierstrassEllipticZeta
