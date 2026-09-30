-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_cleared_auxiliary_polynomial_presentation
-- name    : WeierstrassEllipticZeta.cleared_auxiliary_polynomial_presentation
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T13:37:05.32342+00:00
-- url     : https://prove2.me/theorems/3be7a906-a3e3-4bc0-902f-7ee9d41881bb
-- title:
--   Cleared auxiliary polynomial with separate degree bounds
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and canonical Weierstrass functions $\wp,\wp',\zeta$. Let $v\notin\Lambda$, let $m,\ell$ be nonnegative integers, and let $(c_{ijk})_{0\le i\le m,\,0\le j,k\le\ell}$ be any complex coefficient array. There is a polynomial $P\in\mathbb C[X_0,X_1,X_2,X_3]$ such that every monomial $X_0^{d_0}X_1^{d_1}X_2^{d_2}X_3^{d_3}$ with nonzero coefficient satisfies
--
--   $$d_0\le m,\qquad d_1+d_2+d_3\le5\ell,$$
--
--   and, for every $z$ such that $z,z+v\notin\Lambda$,
--
--   $$P(z,\wp(z),\wp'(z),\zeta(z))=[2(\wp(v)-\wp(z))]^{3\ell}\sum_{i,j,k}c_{ijk}(z+v)^i\wp(z+v)^j\zeta(z+v)^k.$$
--
--   No nonzero-coefficient hypothesis or nonvanishing-denominator hypothesis is imposed. In particular the identity also applies when $\wp(v)=\wp(z)$. The two degree bounds are separate: ordinary degree in $X_0$, and combined degree in the three elliptic/zeta variables.
--
--   An explicit construction sets $b=\wp(v)$, $d=\wp'(v)$, $a=\zeta(v)$ and
--
--   $$A=2(b-X_1),\quad B=-4(X_1+b)(b-X_1)^2+(d-X_2)^2,\quad E=2(X_3+a)(b-X_1)+(d-X_2),$$
--
--   then takes $P=\sum c_{ijk}(X_0+v)^iA^{3\ell-2j-k}B^jE^k$. The exponent is nonnegative because $j,k\le\ell$. The addition identities give the evaluation formula without division.
-- source:
--   Senthil Kumar K (2026), proof of Lemma 9 and equations (5)-(6), https://doi.org/10.1017/S001309152610145X. This derived formulation makes the cleared polynomial Q explicit, for any regular translate v and arbitrary coefficient array. The elliptic degree is a bound on each monomial exponent sum, as needed for bihomogenization; it is not a sum of three separate maximal variable degrees. It uses the division-free addition formulas, and includes vanishing clearing factors and zero integer parameters.

import Definitions.Def_WeierstrassEllipticZeta_Defs
import Mathlib.Algebra.MvPolynomial.Eval

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.cleared_auxiliary_polynomial_presentation
    (L : PeriodPair) (v : ℂ) (hv : v ∉ L.lattice) (m l : ℕ)
    (c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ) :
    ∃ P : MvPolynomial (Fin 4) ℂ,
      (∀ d ∈ P.support, d 0 ≤ m ∧ d 1 + d 2 + d 3 ≤ 5 * l) ∧
      ∀ z : ℂ, z ∉ L.lattice → z + v ∉ L.lattice →
        MvPolynomial.eval ![z, L.weierstrassP z, L.derivWeierstrassP z,
          weierstrassZeta L z] P =
          (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * l) *
            (∑ i, c i * (z + v) ^ i.1.val * L.weierstrassP (z + v) ^ i.2.1.val *
              weierstrassZeta L (z + v) ^ i.2.2.val) := by sorry
