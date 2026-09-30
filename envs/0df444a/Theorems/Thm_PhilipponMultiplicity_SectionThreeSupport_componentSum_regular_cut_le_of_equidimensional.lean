-- Prove2me | Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_componentSum_regular_cut_le_of_equidimensional
-- name    : PhilipponMultiplicity.SectionThreeSupport.componentSum_regular_cut_le_of_equidimensional
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T00:57:09.149052+00:00
-- url     : https://prove2.me/theorems/6d3b4318-c193-4196-a1c7-d9cd814988e4
-- title:
--   Regular-cut degree bound for equidimensional relevant support
-- statement:
--   Let $I$ be a multihomogeneous ideal over a field. Assume that every relevant minimal prime of $I$ has the same Hilbert dimension as $I$. Let $P$ be multihomogeneous of natural multidegree $D$ and regular modulo $I$. Then, for every open locus $U$ of maximal ideals,
--   $$S_UH(I+(P);D)\le H(I;D).$$
--   The component sum uses the actual isolated primary multiplicities. Zero degree entries and empty relevant cuts are allowed. The hypothesis concerns the original ideal's equidimensionality; the dimensions of its cut components are conclusions proved through the geometric component theorem, not additional hypotheses of this statement.
-- source:
--   Philippon (1986), proof of Proposition 3.3, printed pp. 368–370, one-cut estimate for the pure-dimensional slices; https://www.numdam.org/articles/10.24033/bsmf.2060/ . This supporting reduction does not assert the full multi-step proposition.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.SectionThreeSupport.componentSum_regular_cut_le_of_equidimensional
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
(I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I)
    (hdim : ∀ p ∈ I.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension p →
      idealDimension M p = idealDimension M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hregular : IsRegular (Ideal.Quotient.mk I P))
    (U : MaximalOpenLocus M) :
    componentHilbertSum M (I ⊔ Ideal.span {P}) U D ≤ idealDegreeValue M I D := by sorry
