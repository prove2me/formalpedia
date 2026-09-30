-- Prove2me | Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_componentSum_le_of_discarded_zero
-- name    : PhilipponMultiplicity.SectionThreeSupport.componentSum_le_of_discarded_zero
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T10:00:10.635101+00:00
-- url     : https://prove2.me/theorems/ed990135-ae40-4769-a21d-2810dfb79cca
-- title:
--   Primary multiplicities at the endpoint of dimension descent
-- statement:
--   Let $J\subseteq I$ be multihomogeneous ideals in the coordinate ring of a product of projective spaces over any field. Assume that every relevant minimal prime of $J$ which is not an associated prime of $R/I$ has Hilbert dimension zero. For every open set $U$ of maximal ideals and every natural degree vector $d$, the sum $S_UH(I;d)$ of the degree forms of the actual isolated primary components of $I$ meeting $U$ is at most $S_UH(J;d)$. These are the canonical localized primary components, so the comparison retains their scheme multiplicities. Zero entries in $d$ are allowed. This proves the final comparison in the descent, rather than the estimates at its intermediate cuts.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs. The scheme-theoretic endpoint comparison in the proof of Proposition 3.3, printed p. 366. The discarded-prime zero-dimensional bound is the concrete final-stage invariant. The inequalities along the cuts remain separate obligations. https://www.numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.SectionThreeSupport.componentSum_le_of_discarded_zero
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
(J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I)
    (hbound : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      idealDimension M q ≤ 0)
    (U : MaximalOpenLocus M) (D : M.FactorIndex → ℕ) :
    componentHilbertSum M I U D ≤ componentHilbertSum M J U D := by sorry
