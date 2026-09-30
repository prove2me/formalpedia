-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_sigma_projective_coordinates_entire
-- name    : WeierstrassEllipticZeta.sigma_projective_coordinates_entire
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T14:19:52.813645+00:00
-- url     : https://prove2.me/theorems/2e73fcfc-c3f5-4d3d-a435-68e7bce010e9
-- title:
--   Entire sigma projective coordinates with no common zero
-- statement:
--   Let $L$ be a complex period pair, with lattice $\Lambda$ and canonical Weierstrass functions $\wp,\wp',\zeta$. Let $\sigma:\mathbb C\to\mathbb C$ be entire, normalized by $\sigma(0)=0$ and $\sigma'(0)=1$, and suppose
--
--   $$\sigma'(z)=\zeta(z)\sigma(z)\qquad(z\notin\Lambda).$$
--
--   There are five entire functions $S_0,\ldots,S_4$ such that, for every $z\notin\Lambda$,
--
--   $$\big(S_0(z),S_1(z),S_2(z),S_3(z),S_4(z)\big)
--   =\sigma(z)^3\big(1,\wp(z),\wp'(z),\zeta(z),\wp'(z)\zeta(z)+2\wp(z)^2\big).$$
--
--   At every $z\in\mathbb C$ at least one of the five values is nonzero, and $S_2(0)=-2$. Thus these functions give an entire lift, with no common zero, of the five elliptic projective coordinates. The equalities with the meromorphic expressions are asserted off the lattice; the entire functions themselves are defined everywhere.
--
--   An explicit choice, writing $f=\sigma$, $a=f'$, $b=f''$, and $c=f^{(3)}$, is
--
--   $$S_0=f^3,\quad S_1=f(a^2-fb),\quad S_2=-2a^3+3fab-f^2c,\quad S_3=f^2a,\quad S_4=-a^2b+f(2b^2-ac).$$
--
--   In particular the apparent pole in the last coordinate cancels. This statement concerns analytic coordinates only and does not assert an algebraic-group zero estimate.
-- source:
--   Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, the displayed formula for exp_G and the curve phi(z)=exp_G(z,z,0), https://doi.org/10.1017/S001309152610145X. This derived analytic lemma constructs the five sigma-cubed coordinates globally, proves they have no common zero, and fixes S_2(0)=-2. The differential-polynomial formulas and simple-zero argument supply a formal proof of the regularity implicit in the source formula; no group law or zero estimate is asserted.

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.sigma_projective_coordinates_entire (L : PeriodPair)
    (D : EllipticSigmaDifferentialData L) :
    ∃ S : Fin 5 → ℂ → ℂ,
      (∀ j, AnalyticOnNhd ℂ (S j) Set.univ) ∧
      (∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
        S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
          weierstrassZeta L z,
          L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j) ∧
      (∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) ∧ S 2 0 = -2 := by sorry
