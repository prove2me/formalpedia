-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_cohenMacaulayAt_sup_span_of_isRegular
-- name    : PhilipponMultiplicity.Hilbert.cohenMacaulayAt_sup_span_of_isRegular
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T07:07:12.994324+00:00
-- url     : https://prove2.me/theorems/c80a53fc-5cb4-4b64-9644-665a527ee673
-- title:
--   Local Cohen–Macaulayness survives a regular cut
-- statement:
--   Let $R$ be the multihomogeneous coordinate ring over any field, $I$ an ideal, $m$ a maximal ideal, and $P\in R$. Put $A=R_m$ and $B=A/IA$. If $B$ is Cohen–Macaulay in the mission's existing regular-sequence sense and the image of $P$ is a nonzerodivisor in $B$, then $A/(IA+(P))$ is also Cohen–Macaulay in the same sense. The zero localized ring is allowed; a unit equation gives the zero quotient, as required by the existing convention. No homogeneity or infinite-field hypothesis is needed for this local algebraic implication.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, proof of Proposition 3.3, printed p. 367 immediately before Fact C (the regular-cut step cites Northcott, Lessons on rings, modules and multiplicities, Theorem 14, p. 260). https://www.numdam.org/articles/10.24033/bsmf.2060/. A granular algebraic supporting assertion, in the unchanged localized regular-sequence definitions.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open PhilipponMultiplicity
open PhilipponMultiplicity.SectionThreeSupport

theorem PhilipponMultiplicity.Hilbert.cohenMacaulayAt_sup_span_of_isRegular
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (m : MaximalSpectrum M.CoordinateRing)
    (P : M.CoordinateRing)
    (hCM : Hilbert.IsCohenMacaulayAt K M.factorCount M.ambientDimension I m)
    (hreg : IsRegular (Ideal.Quotient.mk
      (I.map (algebraMap M.CoordinateRing (Localization.AtPrime m.asIdeal)))
      (algebraMap M.CoordinateRing (Localization.AtPrime m.asIdeal) P))) :
    Hilbert.IsCohenMacaulayAt K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P}) m := by sorry
