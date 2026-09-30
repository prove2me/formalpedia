-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_closed_parallelepiped_wp_root_count_sharp_boundary
-- name    : WeierstrassEllipticZeta.closed_parallelepiped_wp_root_count_sharp_boundary
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T01:25:44.690464+00:00
-- url     : https://prove2.me/theorems/d2c7715f-5ebe-436f-a280-2d391f3e3da1
-- title:
--   Sharper boundary count for elliptic polynomial roots
-- statement:
--   Let L be a complex period pair and Z a finite subset of its closed basis parallelepiped. Let H be a nonzero complex polynomial. If wp(z) is a root of H for every z in Z outside the period lattice, then
--
--       card(Z) <= 4*deg(H)+4.
--
--   The previously proved coordinate bound was 8*deg(H)+4. This refinement uses the fact that a nonzero period class has at most two representatives in the closed parallelepiped. Only the zero class can have four. Thus card(Z) <= 2*card(Z modulo the lattice)+2. Combining this with the existing period-class bound 2*deg(H)+1 proves the result.
--
--   All boundary and lattice points are included. H can be constant and Z can be empty. No root condition is imposed at lattice points. This is a new boundary-count estimate derived for the mission, not a quoted numerical assertion from the paper.
--
--   For the A.1 whole-fibre anchor list, where deg(H)<=4n, the coordinate bound improves from 32n+4 to 16n+4. The period-class bound 8n+1 is unchanged. No optimality or effective coordinate enumeration is claimed.
-- source:
--   Derived boundary-count refinement for Senthil Kumar K, Appendix A.2, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. These constants are derived here, not quoted from the paper. Every nonzero lattice class has at most two representatives in a closed two-dimensional basis parallelepiped; only the zero class can have four. Thus card(Z)<=2*card(Z/Lambda)+2. Combined with the proved polynomial root class count, this improves the coordinate bound from 8*deg(H)+4 to 4*deg(H)+4, and the A.1 fibre bound from 32n+4 to 16n+4. The 8n+1 period-class bound and geometric constant C are unchanged.

import Definitions.Def_WeierstrassEllipticZeta_SigmaAddition
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Card
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.closed_parallelepiped_wp_root_count_sharp_boundary
    (L : PeriodPair) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z ∈ L.basis.parallelepiped)
    (H : Polynomial ℂ) (hH : H ≠ 0)
    (hroot : ∀ z ∈ Z, z ∉ L.lattice → L.weierstrassP z ∈ H.roots.toFinset) :
    Z.card ≤ 4 * H.natDegree + 4 := by sorry
