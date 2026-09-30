-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_sigma_addition_from_differential
-- name    : WeierstrassEllipticZeta.sigma_addition_from_differential
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T20:36:45.247211+00:00
-- url     : https://prove2.me/theorems/7f89ec84-f8ff-4707-97ac-186b0263e4ba
-- title:
--   Sigma nonvanishing and addition from the normalized differential equation
-- statement:
--   Let $L$ be a complex period pair, let $\Omega$ be its lattice, and let $\wp,\wp',\zeta$ denote its canonical Weierstrass functions. A normalized entire sigma differential datum consists of an entire function $\sigma:\mathbb C\to\mathbb C$ satisfying
--
--   $$\sigma(0)=0,\qquad \sigma'(0)=1,$$
--
--   and the differential equation
--
--   $$\sigma'(z)=\zeta(z)\sigma(z)\qquad(z\notin\Omega).$$
--
--   The datum has no nonvanishing, addition, periodicity, or growth field. It is an interface for the normalized entire solution; the definition itself asserts no existence theorem.
--
--   Suppose such a datum is given. Assume the canonical zeta derivative identity outside the lattice,
--
--   $$\zeta'(z)=-\wp(z),$$
--
--   and, whenever $z,v,z+v\notin\Omega$, the multiplied-out zeta addition identity
--
--   $$2(\wp(v)-\wp(z))\zeta(z+v)=2(\zeta(z)+\zeta(v))(\wp(v)-\wp(z))+\wp'(v)-\wp'(z).$$
--
--   Then the function has no zeros outside the lattice,
--
--   $$\sigma(z)\ne0\qquad(z\notin\Omega),$$
--
--   and for every $z,v\notin\Omega$ it satisfies
--
--   $$\sigma(z+v)\sigma(z-v)=(\wp(v)-\wp(z))\sigma(z)^2\sigma(v)^2.$$
--
--   The sum or difference may belong to the lattice, and no distinctness condition on the two elliptic values is imposed. This result supplies the nonvanishing and addition properties needed for sigma multiplication from the normalized entire differential equation.
-- source:
--   NIST DLMF 23.2(ii), equation (23.2.8), and 23.10(i), equation (23.10.3), https://dlmf.nist.gov/23.2#E8 and https://dlmf.nist.gov/23.10#E3. This conditional formulation derives the latter addition identity and nonvanishing from an entire normalized solution of the former differential equation, using the canonical zeta derivative and addition identities. Its addition conclusion is the sigma identity used immediately after equation (13) in Senthil Kumar K (2026), Section 4, proof of Lemma 5. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.sigma_addition_from_differential
    (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_zeta_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z) :
    (∀ z : ℂ, z ∉ L.lattice → S.sigma z ≠ 0) ∧
      ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice →
        S.sigma (z + v) * S.sigma (z - v) =
          (L.weierstrassP v - L.weierstrassP z) * S.sigma z ^ 2 * S.sigma v ^ 2 := by sorry
