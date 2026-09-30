-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_formula
-- name    : WeierstrassEllipticZeta.zeta_addition_formula
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-04T23:39:22.437811+00:00
-- url     : https://prove2.me/theorems/887e836a-a5cb-4c89-9ce9-50b85be12d0c
-- title:
--   Equation (5): Weierstrass zeta addition identity
-- statement:
--   For any period pair with lattice $\Omega$ and complex $z,v$ such that $z,v,z+v\notin\Omega$, the canonical zeta function satisfies
--   $$2\bigl(\wp(v)-\wp(z)\bigr)\zeta(z+v)=2\bigl(\zeta(z)+\zeta(v)\bigr)\bigl(\wp(v)-\wp(z)\bigr)+\wp'(v)-\wp'(z).$$
--   This is the multiplied-out identity in equation (5). No assumption $\wp(v)\ne\wp(z)$ is imposed; the pole exclusions make the pointwise interpretation explicit.
-- source:
--   Senthil Kumar K, Algebraic independence of values of Weierstrass elliptic and zeta functions, Proceedings of the Edinburgh Mathematical Society (online 17 June 2026), §4, equation (5), https://doi.org/10.1017/S001309152610145X.

import Definitions.Def_WeierstrassEllipticZeta_Defs

namespace WeierstrassEllipticZeta

/-- Senthil Kumar (2026), equation (5), at points where all functions are finite. -/
theorem zeta_addition_formula (L : PeriodPair) (z v : ℂ)
    (hz : z ∉ L.lattice) (hv : v ∉ L.lattice)
    (hzv : z + v ∉ L.lattice) :
    2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
      2 * (weierstrassZeta L z + weierstrassZeta L v) *
        (L.weierstrassP v - L.weierstrassP z) +
      L.derivWeierstrassP v - L.derivWeierstrassP z := by sorry

end WeierstrassEllipticZeta
