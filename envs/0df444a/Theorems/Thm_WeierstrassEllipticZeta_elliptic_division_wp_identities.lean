-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_division_wp_identities
-- name    : WeierstrassEllipticZeta.elliptic_division_wp_identities
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T19:33:15.049174+00:00
-- url     : https://prove2.me/theorems/92bcbd17-4be9-4bc9-aaa7-70e275d7e547
-- title:
--   Elliptic division identities where the denominator is nonzero
-- statement:
--   Let $L$ be a complex period pair, with lattice $\Omega$, invariants $g_2,g_3$, and canonical functions $\wp,\wp',\zeta$. For the fixed integer polynomials and derivation specified below, write
--
--   $$y_z=(g_2/4,g_3/4,\wp(z),\wp'(z),\zeta(z)),\qquad f_n(z)=F_n(y_z).$$
--
--   Assume the canonical elliptic addition identity, for all $z,v,z+v\notin\Omega$:
--
--   $$4(\wp(v)-\wp(z))^2\wp(z+v)=-4(\wp(z)+\wp(v))(\wp(v)-\wp(z))^2+(\wp'(v)-\wp'(z))^2.$$
--
--   Then the conditional elliptic division identities hold:
--
--   $$\operatorname{EllipticDivisionWpIdentities}(L).$$
--
--   The conditional elliptic division identities mean that, for every positive integer $n$ and every $z$ such that
--
--   $$z\notin\Omega,\qquad nz\notin\Omega,\qquad f_n(z)\ne0,$$
--
--   one has
--
--   $$f_n(z)^2\wp(nz)=\wp(z)f_n(z)^2-f_{n-1}(z)f_{n+1}(z),$$
--
--   $$f_n(z)^4\wp'(nz)=f_{2n}(z).$$
--
--   Nonvanishing is a hypothesis of these conditional identities, not a conclusion.
--
--   This isolates the rational elliptic multiplication formulas of Lemma 5. It asserts them only where the division denominator is already nonzero; sigma multiplication supplies the separate nonvanishing argument. There is no sigma, zeta multiplication, or quantitative-bound obligation in this statement.
--
--   Work in the integer polynomial ring in five independent variables, ordered as
--
--   $$(G,H,x,p,Z).$$
--
--   Set
--
--   $$\beta=16(x^3-Gx-H)^2,\qquad
--   \gamma=3x^4-6Gx^2-12Hx-G^2,$$
--
--   $$\delta=2x^6-10Gx^4-40Hx^3-10G^2x^2-8GHx+2G^3-16H^2.$$
--
--   Let $r_n=\operatorname{preNormEDS}'(\beta,\gamma,\delta,n)$ be Mathlib's auxiliary normalized elliptic-divisibility sequence. Explicitly, its initial terms and recurrences are
--
--   $$r_0=0,\quad r_1=r_2=1,\quad r_3=\gamma,\quad r_4=\delta,$$
--
--   $$r_{2k}=r_{k-1}^2r_kr_{k+2}-r_{k-2}r_kr_{k+1}^2\quad(k\ge3),$$
--
--   $$r_{2k+1}=r_{k+2}r_k^3\begin{cases}\beta&k\text{ even},\\1&k\text{ odd}\end{cases}
--   -r_{k-1}r_{k+1}^3\begin{cases}1&k\text{ even},\\\beta&k\text{ odd}\end{cases}\quad(k\ge2).$$
--
--   The reduced division polynomial is
--
--   $$F_n=r_n\begin{cases}p&n\text{ even},\\1&n\text{ odd}.\end{cases}$$
--
--   These are the usual division-polynomial representatives after using the cubic relation to replace even powers of $p$. The even factor is $p$, corresponding to $2y=\wp'$. The signs above correspond to the curve $y^2=x^3-Gx-H$.
--
--   Define the integer polynomial derivation $\mathcal D$ by
--
--   $$\mathcal D(G,H,x,p,Z)=(0,0,p,6x^2-2G,-x).$$
-- source:
--   Senthil Kumar K (2026), Section 4 Lemma 5, the first two identities of equation (12). The paper cites Washington, Elliptic Curves: Number Theory and Cryptography, Lemmas 9.28 and 9.32, and Lang, Elliptic Functions, Theorem 1.1 p. 34. Here these are multiplied out and restricted to the locus where the evaluated canonical division polynomial is nonzero; nonvanishing and the zeta identity are separate conclusions of the sigma argument. The polynomials are the explicit Mathlib preNormEDS reduced representatives already defined for this mission. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_SigmaAddition

open MvPolynomial WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_division_wp_identities
    (L : PeriodPair)
    (h_wp_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
        -4 * (L.weierstrassP z + L.weierstrassP v) *
          (L.weierstrassP v - L.weierstrassP z) ^ 2 +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2) :
    EllipticDivisionWpIdentities L := by sorry
