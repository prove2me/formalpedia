-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_wp_addition_formula
-- name    : WeierstrassEllipticZeta.wp_addition_formula
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-04T23:39:39.538363+00:00
-- url     : https://prove2.me/theorems/00522402-ea80-473e-9206-63ef770c0d45
-- title:
--   Equation (6): Weierstrass elliptic addition identity
-- statement:
--   For any period pair with lattice $\Omega$ and complex $z,v$ such that $z,v,z+v\notin\Omega$, the Weierstrass elliptic function satisfies
--   $$4\bigl(\wp(v)-\wp(z)\bigr)^2\wp(z+v)=-4\bigl(\wp(z)+\wp(v)\bigr)\bigl(\wp(v)-\wp(z)\bigr)^2+\bigl(\wp'(v)-\wp'(z)\bigr)^2.$$
--   This is the multiplied-out identity in equation (6). No assumption $\wp(v)\ne\wp(z)$ is imposed; the pole exclusions make the pointwise interpretation explicit.
-- source:
--   Senthil Kumar K, Algebraic independence of values of Weierstrass elliptic and zeta functions, Proceedings of the Edinburgh Mathematical Society (online 17 June 2026), §4, equation (6), https://doi.org/10.1017/S001309152610145X.

import Definitions.Def_WeierstrassEllipticZeta_Defs

namespace WeierstrassEllipticZeta

/-- Senthil Kumar (2026), equation (6), at points where all functions are finite. -/
theorem wp_addition_formula (L : PeriodPair) (z v : ℂ)
    (hz : z ∉ L.lattice) (hv : v ∉ L.lattice)
    (hzv : z + v ∉ L.lattice) :
    4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
      -4 * (L.weierstrassP z + L.weierstrassP v) *
        (L.weierstrassP v - L.weierstrassP z) ^ 2 +
      (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2 := by sorry

end WeierstrassEllipticZeta
