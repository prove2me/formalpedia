-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_wp_contact_dimension_bound
-- name    : WeierstrassEllipticZeta.wp_contact_dimension_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-22T20:54:44.534365+00:00
-- url     : https://prove2.me/theorems/b6bc086f-5654-4f41-bdb9-a9116727ad8c
-- title:
--   Elliptic contact dimension bounded by distinct Weierstrass values
-- statement:
--   Let G be the fixed elliptic chart geometry used in the A.1 formalization, with period lattice Λ and Weierstrass function ℘. Let Y be any finite set of complex numbers and let N be any nonnegative integer. Remove the lattice points, writing Z = Y ∖ Λ. In the polynomial ring in the four first-chart coordinates, let I be the intersection of the order-N contact ideals at the points of Z, and let x be the image of the elliptic coordinate X₁ in the quotient by I.
--
--   Then x is integral over ℂ, and
--
--   $$\dim_{\mathbb C}\mathbb C[x]\ \le\ N\,|\wp(Z)|\ \le\ N\,|Y\bmod\Lambda|.$$
--
--   Here ℘(Z) is the set of distinct elliptic values, so repeated values count once. The assertion includes N = 0 and Z empty, when the quotient is the zero ring. It requires no choice of auxiliary polynomial Q, no bidegree bound, and no chart certificate beyond the contact-ideal axioms already included in G.
--
--   This is a local dimension estimate. It does not bound the number of period classes in terms of the bidegree and therefore does not by itself establish A.1's uniform global multiplicity estimate.
-- source:
--   Derived elliptic-value annihilator and contact-dimension bound for Senthil Kumar K (2026), Appendix A.2, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. The lemma is derived here, not quoted from the paper. For Z=Y minus the period lattice, the monic polynomial (product over a in wp(Z) of (T-a))^N annihilates the elliptic coordinate in the order-N contact quotient. The minimal-polynomial power basis gives dimension <= N*|wp(Z)| <= N*|Y modulo lattice|. Pinned Mathlib ingredients: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Adjoin/PowerBasis.lean and Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean. The resulting sketch connects https://prove2.me/theorems/0a5b5931-7355-4844-a69c-f0c5659be7aa to the existing analytic obstruction https://prove2.me/theorems/9acd36b2-ab77-4168-8242-cb12676662c4 with C=7*C0. No new Open child or improvement to the global geometric estimate is claimed.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.RingTheory.Adjoin.PowerBasis
open WeierstrassEllipticZeta
open scoped Classical

theorem WeierstrassEllipticZeta.wp_contact_dimension_bound
    (G : Frontier.Geometry) (Y : Finset ℂ) (N : ℕ) :
    let Z := Y.filter (fun z => z ∉ G.L.lattice)
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ 0
        (extensionChartCoordinates G.S 0 z.val) N
    let x := Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 4))
    IsIntegral ℂ x ∧
      Module.finrank ℂ (Algebra.adjoin ℂ ({x} : Set _)) ≤
        N * (Z.image G.L.weierstrassP).card ∧
      N * (Z.image G.L.weierstrassP).card ≤
        N * (G.L.lattice.mkQ '' (Y : Set ℂ)).ncard := by sorry
