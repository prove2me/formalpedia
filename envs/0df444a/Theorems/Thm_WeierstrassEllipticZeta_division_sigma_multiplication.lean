-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_division_sigma_multiplication
-- name    : WeierstrassEllipticZeta.division_sigma_multiplication
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T19:33:15.215621+00:00
-- url     : https://prove2.me/theorems/5d6cbd21-352a-4b17-a314-754df8a9adf7
-- title:
--   Sigma multiplication, nonvanishing, and zeta values on regular multiples
-- statement:
--   Let $L$ be a complex period pair, with lattice $\Omega$, invariants $g_2,g_3$, and canonical functions $\wp,\wp',\zeta$. For the fixed integer polynomials and derivation specified below, write
--
--   $$y_z=(g_2/4,g_3/4,\wp(z),\wp'(z),\zeta(z)),\qquad f_n(z)=F_n(y_z).$$
--
--   Assume a normalized sigma datum, the canonical derivative identity $\zeta'=-\wp$ outside the lattice, and the conditional elliptic division identities, all specified below. Let $n\ge1$ and let $u\in\mathbb C$ satisfy
--
--   $$ku\notin\Omega\qquad(1\le k\le n).$$
--
--   Then
--
--   $$\sigma(nu)=(-1)^{n+1}\sigma(u)^{n^2}f_n(u),\qquad f_n(u)\ne0,$$
--
--   $$nf_n(u)\zeta(nu)=n^2f_n(u)\zeta(u)+(\mathcal D F_n)(y_u).$$
--
--   For positive $n$, the sign displayed here is the same as $(-1)^{n-1}$ in equation (13). This result establishes the sigma multiplication identity, denominator nonvanishing, and the zeta multiplication identity on a finite block of regular multiples. It uses only the first of the two conditional elliptic identities. It supplies the analytic induction and differentiation step needed to combine rational elliptic formulas into full multiplication presentations.
--
--   A normalized sigma datum is a function $\sigma:\mathbb C\to\mathbb C$ satisfying
--
--   $$\sigma(0)=0,\qquad \sigma'(0)=1,$$
--
--   and, at every $z\notin\Omega$, differentiability together with
--
--   $$\sigma(z)\ne0,\qquad \sigma'(z)=\zeta(z)\sigma(z).$$
--
--   For every $z,v\notin\Omega$ it also satisfies the multiplied-out addition identity
--
--   $$\sigma(z+v)\sigma(z-v)=(\wp(v)-\wp(z))\sigma(z)^2\sigma(v)^2.$$
--
--   The sum and difference may belong to the lattice. This interface records exactly the sigma properties used here; it does not assert any growth estimate.
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
--   Senthil Kumar K (2026), Section 4 Lemma 5, equations (12) and (13) and the induction immediately following (13). This is the conditional sigma argument under explicitly stated sigma addition and rational elliptic multiplication hypotheses. Finite regularity of multiples 1 through n is retained to justify cancellation and local differentiation. The proof also derives the duplication case from normalized sigma addition and identifies the complex derivative with the polynomial derivation. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_SigmaAddition

open MvPolynomial WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.division_sigma_multiplication (L : PeriodPair) (S : EllipticSigmaData L)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_wp_division : EllipticDivisionWpIdentities L)
    (u : ℂ) (n : ℕ) (hn : 0 < n)
    (h_regular : ∀ k : ℕ, 0 < k → k ≤ n → (k : ℂ) * u ∉ L.lattice) :
    let e := eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L u)
    let f := fun k => e (ellipticDivisionPolynomial k)
    S.sigma ((n : ℂ) * u) = (-1) ^ (n + 1) * S.sigma u ^ (n ^ 2) * f n ∧
      f n ≠ 0 ∧
      (n : ℂ) * f n * weierstrassZeta L (n * u) =
        (n : ℂ) ^ 2 * f n * weierstrassZeta L u +
          e (ellipticMultipleDerivation (ellipticDivisionPolynomial n)) := by sorry
