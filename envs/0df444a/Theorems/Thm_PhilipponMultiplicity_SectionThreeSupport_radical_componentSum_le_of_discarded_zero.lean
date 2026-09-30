-- Prove2me | Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_radical_componentSum_le_of_discarded_zero
-- name    : PhilipponMultiplicity.SectionThreeSupport.radical_componentSum_le_of_discarded_zero
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T09:12:56.401032+00:00
-- url     : https://prove2.me/theorems/ee10c1e1-2164-421a-8348-d0225b54b8a3
-- title:
--   Radical component sum at the end of the dimension descent
-- statement:
--   Let $J\subseteq I$ be multihomogeneous ideals in the coordinate ring of a product of projective spaces over any field. Suppose every relevant minimal prime of $J$ that is not an associated prime of $R/I$ has Hilbert dimension zero. Then, for every open set $U$ of maximal ideals and every natural multidegree $d$, the sum of degree forms of the relevant components of $\sqrt I$ meeting $U$ is at most the corresponding sum for $\sqrt J$. The component sums and degrees are the existing canonical localized-component and Hilbert-polynomial definitions. This is the final radical comparison after the dimension descent, not the bound on the intermediate cutting steps.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, proof of Proposition 3.3, printed pp. 366–368. The geometric induction and final radical comparison are extracted as granular supporting assertions; the numerical bounds along the cuts are separate obligations. https://www.numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport

theorem PhilipponMultiplicity.SectionThreeSupport.radical_componentSum_le_of_discarded_zero
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
(J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I)
    (hbound : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      idealDimension M q ≤ 0)
    (U : MaximalOpenLocus M) (D : M.FactorIndex → ℕ) :
    componentHilbertSum M I.radical U D ≤ componentHilbertSum M J.radical U D := by sorry
