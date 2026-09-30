-- Prove2me | Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_componentSum_le_degreeValue_of_equidimensional
-- name    : PhilipponMultiplicity.SectionThreeSupport.componentSum_le_degreeValue_of_equidimensional
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T23:12:19.434475+00:00
-- url     : https://prove2.me/theorems/6e984aca-9b96-46cd-a8e3-bd879418b3c0
-- title:
--   Open-locus component sum bounded by the equidimensional Hilbert degree
-- statement:
--   Let $I$ be a multihomogeneous ideal in a multiprojective coordinate ring over any field. Suppose every relevant minimal prime of $I$ has the same Hilbert dimension as $I$. For every open locus $U$ of maximal ideals and every natural degree vector $d$,
--   $$S_UH(I;d)\le H(I;d).$$
--   The left sum uses the actual canonical isolated primary components meeting $U$, with multiplicities. Zero entries of $d$ and empty relevant support are included. The equidimensionality premise is an explicit hypothesis.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs. Proof of Proposition 3.3, printed pp. 368–370, where equidimensional component sums are compared with the Hilbert form. The equidimensionality hypothesis is explicit. https://www.numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.SectionThreeSupport.componentSum_le_degreeValue_of_equidimensional
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
(I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I)
    (hdim : ∀ q ∈ I.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      idealDimension M q = idealDimension M I)
    (U : MaximalOpenLocus M) (d : M.FactorIndex → ℕ) :
    componentHilbertSum M I U d ≤ idealDegreeValue M I d := by sorry
