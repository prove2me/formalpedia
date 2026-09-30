-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_frobenius_stickelberger
-- name    : WeierstrassEllipticZeta.frobenius_stickelberger
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-05T01:30:04.561647+00:00
-- url     : https://prove2.me/theorems/6f5b34e3-7e17-42e1-b0d8-c901c6442b4a
-- title:
--   Frobenius–Stickelberger identity for the Weierstrass zeta function
-- statement:
--   Let $L$ be any complex period pair, and let $\wp_L$ and $\zeta_L$ be the canonical Weierstrass functions of its lattice $\Omega$. For $z,v,z+v\notin\Omega$,
--
--   $$
--   \bigl(\zeta_L(z+v)-\zeta_L(z)-\zeta_L(v)\bigr)^2
--   =\wp_L(z)+\wp_L(v)+\wp_L(z+v).
--   $$
--
--   This is the Frobenius–Stickelberger identity with third argument $-z-v$, using oddness of $\zeta_L$, evenness of $\wp_L$, and $\zeta_L'=-\wp_L$. It has no restriction on equality of the two Weierstrass values or on vanishing of their derivatives, and no arithmetic hypothesis on the lattice.
-- source:
--   NIST DLMF §23.10(i), equation 23.10.6, https://dlmf.nist.gov/23.10.E6, with u=z and w=−z−v, using parity and ζ′=−℘ from §23.2. The complete proof uses quasi-periodicity, removable singularities, and Liouville’s theorem.

import Definitions.Def_WeierstrassEllipticZeta_Defs

namespace WeierstrassEllipticZeta

theorem frobenius_stickelberger (L : PeriodPair) (z v : ℂ)
    (hz : z ∉ L.lattice) (hv : v ∉ L.lattice) (hzv : z + v ∉ L.lattice) :
    (weierstrassZeta L (z + v) - weierstrassZeta L z - weierstrassZeta L v) ^ 2 =
      L.weierstrassP z + L.weierstrassP v + L.weierstrassP (z + v) := by sorry

end WeierstrassEllipticZeta
