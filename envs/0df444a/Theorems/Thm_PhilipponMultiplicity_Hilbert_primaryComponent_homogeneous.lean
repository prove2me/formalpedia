-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_primaryComponent_homogeneous
-- name    : PhilipponMultiplicity.Hilbert.primaryComponent_homogeneous
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T10:00:16.740428+00:00
-- url     : https://prove2.me/theorems/973f8f11-0767-4dc9-aef0-cc625397226b
-- title:
--   Canonical primary components are multihomogeneous
-- statement:
--   Let $I$ be a multihomogeneous ideal in the coordinate ring of a product of projective spaces over any field, and let $q$ be a minimal prime of $I$. The canonical isolated primary component $Q_q(I)=IR_q\cap R$ is multihomogeneous. This uses the actual extension to the prime localization and contraction to the coordinate ring, rather than a choice of a homogeneous component as a new definition.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs. The homogeneous isolated-primary-component assertion used in Section 3, printed pp. 362 and 365; the localized contraction is shown to equal a member of a genuine homogeneous primary decomposition. https://www.numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.primaryComponent_homogeneous
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
(I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (q : PrimeSpectrum M.CoordinateRing)
    (hq : q.asIdeal ∈ I.minimalPrimes) :
    IsMultihomogeneousIdeal M (primaryComponent K M.factorCount M.ambientDimension I q) := by sorry
