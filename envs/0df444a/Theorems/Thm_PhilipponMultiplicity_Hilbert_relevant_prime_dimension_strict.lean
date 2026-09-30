-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_relevant_prime_dimension_strict
-- name    : PhilipponMultiplicity.Hilbert.relevant_prime_dimension_strict
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T01:02:12.921932+00:00
-- url     : https://prove2.me/theorems/ba073840-cd1f-4894-ab5f-8c2340031512
-- title:
--   Proper inclusion of relevant homogeneous primes strictly lowers dimension
-- statement:
--   If $Q\subsetneq R$ are multihomogeneous prime ideals and $R$ is multiprojectively relevant, then the total degree of the actual Hilbert polynomial of $R$ is strictly smaller than that of $Q$. This includes the boundary where $R$ has projective dimension zero and works over every field.
-- source:
--   Supporting commutative algebra for Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, §3, Lemma 3.2, printed p. 364, https://www.numdam.org/articles/10.24033/bsmf.2060/. Philippon refers to the classical homogeneous argument and van der Waerden (1928), Theorem 8 p. 758 and §32 p. 767. This is a proved intermediate step of that associativity argument, not an additional numbered assertion in Philippon.

import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.relevant_prime_dimension_strict
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (Q R : Ideal M.CoordinateRing)
    (hQ : Q.IsPrime) (hR : R.IsPrime)
    (hQhom : IsMultihomogeneousIdeal M Q) (hRhom : IsMultihomogeneousIdeal M R)
    (hRrel : IsRelevant K M.factorCount M.ambientDimension R) (hlt : Q < R) :
    idealDimension M R < idealDimension M Q := by sorry
