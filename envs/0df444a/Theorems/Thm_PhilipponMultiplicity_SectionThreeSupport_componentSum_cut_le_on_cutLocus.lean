-- Prove2me | Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_componentSum_cut_le_on_cutLocus
-- name    : PhilipponMultiplicity.SectionThreeSupport.componentSum_cut_le_on_cutLocus
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T12:13:17.815715+00:00
-- url     : https://prove2.me/theorems/64c9d86b-e9a4-4e55-95ef-81c78d994267
-- title:
--   Proposition 3.3: remaining primary-multiplicity comparison for one cut
-- statement:
--   Let $J\subseteq I$ with $J$ multihomogeneous, and let $P\in I$ be homogeneous of exact natural multidegree $D$. Assume that $P$ avoids every relevant minimal prime of $J$ that is not associated to $I$. On the original open set $U$, remove the irrelevant support and the retained isolated components to form $U_J$. If $J$ is locally Cohen–Macaulay on $U_J$, prove $$S_UH(J+(P);D)\le S_UH(J;D).$$ The sums retain the canonical primary multiplicities. Cohen–Macaulayness is required only on the actual current locus, not on all of $U$. This is the remaining numerical step; the changing loci, local equality, finite induction and endpoint comparison are already proved.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs. Scheme-theoretic one-cut comparison in Proposition 3.3, printed pp. 369–370, using Facts D and E and Lemmas 3.1 and 3.2. No change to the full original Proposition 3.3 is made. https://www.numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_CutLocus
set_option autoImplicit false
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport

theorem PhilipponMultiplicity.SectionThreeSupport.componentSum_cut_le_on_cutLocus
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (J I : Ideal M.CoordinateRing) (hJ : IsMultihomogeneousIdeal M J) (hJI : J ≤ I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hPI : P ∈ I) (U : MaximalOpenLocus M)
    (hCM : IsLocallyCohenMacaulayOn M J (cutLocus M J I U))
    (havoid : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → P ∉ q) :
    componentHilbertSum M (J ⊔ Ideal.span {P}) U D ≤
      componentHilbertSum M J U D := by sorry
