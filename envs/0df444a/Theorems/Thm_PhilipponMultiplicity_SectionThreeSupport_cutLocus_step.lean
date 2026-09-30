-- Prove2me | Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_cutLocus_step
-- name    : PhilipponMultiplicity.SectionThreeSupport.cutLocus_step
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T12:13:12.053521+00:00
-- url     : https://prove2.me/theorems/95b3c800-57e6-4bcf-8276-8e4db0a4acf7
-- title:
--   Proposition 3.3: Cohen–Macaulayness and new components on the shrinking loci
-- statement:
--   Let $J\subseteq I$, with $J$ multihomogeneous, and let $P\in I$ be regular modulo the intersection of the discarded relevant isolated primary components of $J$. Let $U_J$ be the original open locus $U$ with the irrelevant support and retained isolated components removed. If $J$ is locally Cohen–Macaulay on $U_J$, then the next locus $U_{J+(P)}$ is contained in $U_J$, and $J+(P)$ is locally Cohen–Macaulay on both loci. Every relevant minimal prime of $J+(P)$ meeting $U$ that is not an old retained minimal prime also meets $U_J$. All ideals and primary components are the actual localization-defined objects; no local-equality hypothesis is assumed.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs. Actual shrinking-open-locus argument and Fact C, printed pp. 366–367, and the new-component locus equivalence on printed p. 368, in the proof of Proposition 3.3. https://www.numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_CutLocus
set_option autoImplicit false
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport

theorem PhilipponMultiplicity.SectionThreeSupport.cutLocus_step
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hJI : J ≤ I)
    (P : M.CoordinateRing) (hPI : P ∈ I) (U : MaximalOpenLocus M)
    (hCM : IsLocallyCohenMacaulayOn M J (cutLocus M J I U))
    (hreg : IsRegular (Ideal.Quotient.mk (discardedRelevantPart M J I) P)) :
    (cutLocus M (J ⊔ Ideal.span {P}) I U ≤ cutLocus M J I U) ∧
    IsLocallyCohenMacaulayOn M (J ⊔ Ideal.span {P}) (cutLocus M J I U) ∧
    IsLocallyCohenMacaulayOn M (J ⊔ Ideal.span {P})
      (cutLocus M (J ⊔ Ideal.span {P}) I U) ∧
    (∀ q ∈ (J ⊔ Ideal.span {P}).minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U →
      ¬ (q ∈ J.minimalPrimes ∧
        q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)) →
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q (cutLocus M J I U)) := by sorry
