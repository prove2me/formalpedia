-- Prove2me | Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_embedded_avoidance_on_open
-- name    : PhilipponMultiplicity.SectionThreeSupport.embedded_avoidance_on_open
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T02:39:26.331291+00:00
-- url     : https://prove2.me/theorems/4c9f4550-41f4-4344-bef8-125d8ad648d6
-- title:
--   Fact E — embedded components avoid the Cohen–Macaulay open locus
-- statement:
--   For a genuine minimal homogeneous primary decomposition of $I$ and an open set $U$ on which $I$ is locally Cohen–Macaulay, no embedded component meets $U$. If every associated prime of another quotient $R/L$ meets $U$, no embedded radical is contained in such a prime, and there is an element in all embedded components that is regular modulo $L$.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, Fact E, printed p. 369, https://www.numdam.org/articles/10.24033/bsmf.2060/. A granular supporting assertion for the original Section 3 statements; definitions are unchanged.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.SectionThreeSupport.embedded_avoidance_on_open
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (D : PrimaryDecomposition M I)
    (U : MaximalOpenLocus M) (hU : IsLocallyCohenMacaulayOn M I U) :
    (∀ i : Fin D.count, D.IsEmbedded i →
      ¬ Hilbert.MeetsOpen K M.factorCount M.ambientDimension (D.component i).radical U) ∧
    (∀ L : Ideal M.CoordinateRing,
      (∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ L),
        Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U) →
      (∀ i : Fin D.count, D.IsEmbedded i →
        ∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ L),
          ¬ (D.component i).radical ≤ q) ∧
      ∃ Q ∈ D.embeddedIntersection, IsRegular (Ideal.Quotient.mk L Q)) := by sorry
