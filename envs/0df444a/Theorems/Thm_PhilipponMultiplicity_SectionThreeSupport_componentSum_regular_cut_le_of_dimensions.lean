-- Prove2me | Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_componentSum_regular_cut_le_of_dimensions
-- name    : PhilipponMultiplicity.SectionThreeSupport.componentSum_regular_cut_le_of_dimensions
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T23:12:20.547497+00:00
-- url     : https://prove2.me/theorems/7352f1e8-63d3-4c52-a843-f518405e55a6
-- title:
--   Regular-cut degree bound from component dimensions, allowing zero entries
-- statement:
--   Let $I$ be a multihomogeneous ideal over any field, and let $P$ be a multihomogeneous polynomial of exact natural multidegree $D$ whose class is regular on $R/I$. Assume every relevant minimal prime $q$ of $I+(P)$ has Hilbert dimension exactly one less than that of $I$. Then, for every open locus $U$ of maximal ideals,
--   $$S_UH(I+(P);D)\le H(I;D).$$
--   The sum retains actual primary multiplicities. Zero entries of $D$ and cuts with empty relevant support are allowed. This proves the numerical implication from the stated component dimensions; it does not prove that geometric dimension hypothesis or the full multi-step Proposition 3.3.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs. Numerical degree calculation in Lemma 3.1 and the proof of Proposition 3.3, printed pp. 363 and 368–370. This is a supporting conditional result: component dimension drop remains a geometric premise, and zero degree entries are explicitly included. It does not strengthen or replace the original Proposition 3.3. https://www.numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.SectionThreeSupport.componentSum_regular_cut_le_of_dimensions
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
(I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hregular : IsRegular (Ideal.Quotient.mk I P))
    (hcut : ∀ q ∈ (I ⊔ Ideal.span {P}).minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      idealDimension M q + 1 = idealDimension M I)
    (U : MaximalOpenLocus M) :
    componentHilbertSum M (I ⊔ Ideal.span {P}) U D ≤ idealDegreeValue M I D := by sorry
