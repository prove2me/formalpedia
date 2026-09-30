-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_cohenMacaulayAt_associated_isMinimal
-- name    : PhilipponMultiplicity.Hilbert.cohenMacaulayAt_associated_isMinimal
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T02:39:51.194447+00:00
-- url     : https://prove2.me/theorems/b24da554-0c25-41ba-9533-b0f2f315013f
-- title:
--   Cohen–Macaulay localization excludes embedded associated primes
-- statement:
--   Let $I$ be an ideal in the polynomial coordinate ring and $m$ a maximal ideal. Assume the actual localized quotient $(R/I)_m$ satisfies the mission’s regular-sequence definition of Cohen–Macaulayness. Every associated prime of $R/I$ contained in $m$ is minimal over $I$. The zero localized quotient is included in the definition and must be handled.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, unmixedness used in Fact E, printed p. 369, https://www.numdam.org/articles/10.24033/bsmf.2060/. A granular supporting assertion for the original Section 3 statements; definitions are unchanged.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.cohenMacaulayAt_associated_isMinimal
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (m : MaximalSpectrum M.CoordinateRing)
    (hCM : Hilbert.IsCohenMacaulayAt K M.factorCount M.ambientDimension I m)
    (q : Ideal M.CoordinateRing)
    (hq : q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I))
    (hqm : q ≤ m.asIdeal) : q ∈ I.minimalPrimes := by sorry
