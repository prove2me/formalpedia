-- Prove2me | Theorems.Thm_PhilipponMultiplicity_RadicalIntersection_radical_componentSum_cut_le
-- name    : PhilipponMultiplicity.RadicalIntersection.radical_componentSum_cut_le
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T10:27:10.269036+00:00
-- url     : https://prove2.me/theorems/d2b4f88c-1a30-4843-b1d6-e5ed4d5633a9
-- title:
--   Reduced component degree does not increase under a homogeneous cut
-- statement:
--   Let $I$ be a multihomogeneous ideal over any field and $P$ a multihomogeneous equation of exact natural multidegree $D$. For every open locus $U$ of maximal ideals, $$S_UH(\sqrt{I+(P)};D)\le S_UH(\sqrt I;D).$$ The component sums use the actual relevant minimal primes and Hilbert degrees. No regularity or equidimensionality of $I$ is assumed. Zero entries of $D$ and empty relevant support are included.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs. Supporting reduced per-cut inequality in Proposition 3.3, printed p. 368. The proof expands the paper’s component decomposition into a finite cover by cuts of its original minimal primes. https://www.numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.RadicalIntersection.radical_componentSum_cut_le
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) (U : MaximalOpenLocus M) :
    componentHilbertSum M (I ⊔ Ideal.span {P}).radical U D ≤
      componentHilbertSum M I.radical U D := by sorry
