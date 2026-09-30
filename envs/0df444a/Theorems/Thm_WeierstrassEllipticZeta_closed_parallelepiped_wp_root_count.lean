-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_closed_parallelepiped_wp_root_count
-- name    : WeierstrassEllipticZeta.closed_parallelepiped_wp_root_count
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T01:08:49.6237+00:00
-- url     : https://prove2.me/theorems/e4488545-764f-430c-bff5-ec6c2ed98334
-- title:
--   Polynomial root control bounds closed-period-domain representatives
-- statement:
--   Let L be a complex period pair, Z a finite subset of its **closed** basis parallelepiped, and H a nonzero polynomial over C. Suppose every z in Z outside the period lattice has wp(z) among the roots of H. Then
--
--   - the number of period classes represented by Z is at most 2 deg(H)+1;
--   - the number of coordinates in Z is at most 8 deg(H)+4.
--
--   The additive terms include the possible lattice class. Closed boundary points are retained: one lattice class can have up to four representatives in the closed parallelepiped. No injectivity of its projection to the quotient is assumed. H may be constant and Z may be empty. No condition is imposed on H at lattice points.
--
--   In A.1, the already proved whole-fibre polynomial has degree at most 4n, so the bounds become 8n+1 period classes and 32n+4 actual anchor coordinates. The root-count bound is derived here; these constants are not quoted from the paper. No optimality or effective enumeration algorithm is asserted.
-- source:
--   Derived closed-domain counting lemma for Senthil Kumar K, Appendix A.2, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. These numerical constants are derived here, not quoted from the paper. The proved sigma-addition root-count theorem gives at most 2*deg(H)+1 lattice classes. A closed fundamental parallelepiped has at most four representatives per lattice class, giving 8*deg(H)+4 coordinates. Applied to the existing degree-4n fibre spectrum, this gives 8n+1 classes and 32n+4 coordinates, including the lattice class and boundary duplicates. The geometric cost-product upper bound remains Open and its constant C is preserved.

import Definitions.Def_WeierstrassEllipticZeta_SigmaAddition
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Card
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.closed_parallelepiped_wp_root_count (L : PeriodPair) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z ∈ L.basis.parallelepiped)
    (H : Polynomial ℂ) (hH : H ≠ 0)
    (hroot : ∀ z ∈ Z, z ∉ L.lattice → L.weierstrassP z ∈ H.roots.toFinset) :
    (L.lattice.mkQ '' (Z : Set ℂ)).ncard ≤ 2 * H.natDegree + 1 ∧
      Z.card ≤ 8 * H.natDegree + 4 := by sorry
