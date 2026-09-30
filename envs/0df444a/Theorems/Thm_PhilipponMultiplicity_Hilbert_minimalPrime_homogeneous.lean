-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_minimalPrime_homogeneous
-- name    : PhilipponMultiplicity.Hilbert.minimalPrime_homogeneous
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T02:38:46.188508+00:00
-- url     : https://prove2.me/theorems/69081264-1609-4b2e-b963-8a431ba530a7
-- title:
--   Minimal primes of a multihomogeneous ideal are multihomogeneous
-- statement:
--   Let $I$ be a multihomogeneous ideal in the coordinate ring of a product of projective spaces over a field. Every actual minimal prime $q$ of $I$ is multihomogeneous. This supplies the homogeneous prime hypotheses in dimension comparisons.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, §3, pp. 361–365; supporting graded commutative algebra, https://www.numdam.org/articles/10.24033/bsmf.2060/. A granular supporting assertion for the original Section 3 statements; definitions are unchanged.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.minimalPrime_homogeneous
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (I Q : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hQ : Q ∈ I.minimalPrimes) :
    IsMultihomogeneousIdeal M Q := by sorry
