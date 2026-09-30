-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_exists_relevant_minimalPrime_dimension_eq
-- name    : PhilipponMultiplicity.Hilbert.exists_relevant_minimalPrime_dimension_eq
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T07:02:10.921619+00:00
-- url     : https://prove2.me/theorems/a909f1b8-9294-4ab3-b2d1-fd355c6da43e
-- title:
--   A relevant minimal component attains the Hilbert dimension
-- statement:
--   Every projectively nontrivial multihomogeneous ideal $I$ over a field has a relevant minimal prime $q$ with
--   $$\deg F_q=\deg F_I,$$
--   where $F_I$ is the actual eventual multigraded Hilbert polynomial. This includes nonreduced ideals and Hilbert dimension zero. No Krull-dimension comparison is assumed.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, §3, printed pp. 362–364; https://www.numdam.org/articles/10.24033/bsmf.2060/ . Supporting consequence of the homogeneous prime-filtration proof of Lemma 3.2; it selects an actual minimal prime, rather than assuming a component attaining the dimension.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.exists_relevant_minimalPrime_dimension_eq
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
(I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hNontrivial : IsNontrivialIdeal M I) :
    ∃ q ∈ I.minimalPrimes, IsRelevant K M.factorCount M.ambientDimension q ∧
      idealDimension M q = idealDimension M I := by sorry
