-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_exists_elliptic_sigma_addition_data
-- name    : WeierstrassEllipticZeta.exists_elliptic_sigma_addition_data
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T19:33:18.330988+00:00
-- url     : https://prove2.me/theorems/ae65c632-4a45-4477-a284-4df6d615c180
-- title:
--   Existence of normalized Weierstrass sigma addition data
-- statement:
--   Let $L$ be a complex period pair, with lattice $\Omega$ and its canonical Weierstrass functions $\wp,\wp',\zeta$.
--
--   Assume, at every point outside $\Omega$, the canonical derivative identity
--
--   $$\zeta'(z)=-\wp(z).$$
--
--   Assume also, for every $z,v,z+v\notin\Omega$, the multiplied-out zeta addition identity
--
--   $$2(\wp(v)-\wp(z))\zeta(z+v)=2(\zeta(z)+\zeta(v))(\wp(v)-\wp(z))+\wp'(v)-\wp'(z).$$
--
--   Then there exists a normalized sigma datum for $L$:
--
--   $$\operatorname{EllipticSigmaData}(L)\ne\varnothing.$$
--
--   Its required properties are the following.
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
--   This is the sigma-function input to the induction proving equation (13) of Lemma 5. The normalization at zero and the addition formula include the coincident-input case needed for duplication. Neither division-polynomial identities nor growth estimates are part of this existence statement.
-- source:
--   Senthil Kumar K (2026), Section 4 proof of Lemma 5, equations (13) and the sigma addition identity displayed after it; see the paper's reference to Whittaker and Watson, A Course of Modern Analysis, Example 1 p. 451 and Exercise 20.24. The standard normalization sigma(0)=0, sigma-prime(0)=1 and logarithmic derivative sigma-prime/sigma=zeta are made explicit, as is nonvanishing off the period lattice. This existence statement supplies those classical sigma facts and contains no division-polynomial or growth claims. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_SigmaAddition

open MvPolynomial WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.exists_elliptic_sigma_addition_data
    (L : PeriodPair)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_zeta_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z) :
    Nonempty (EllipticSigmaData L) := by sorry
