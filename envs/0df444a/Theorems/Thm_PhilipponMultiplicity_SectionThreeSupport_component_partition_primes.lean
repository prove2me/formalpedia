-- Prove2me | Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_component_partition_primes
-- name    : PhilipponMultiplicity.SectionThreeSupport.component_partition_primes
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T02:38:53.408752+00:00
-- url     : https://prove2.me/theorems/ae9b2022-bfa9-4971-9b76-5b64a73ba474
-- title:
--   Fact B — retained and discarded isolated primes
-- statement:
--   Let $J\subseteq I$ be ideals in the multiprojective coordinate ring. Every associated prime of $R/I$ contains a minimal prime of $J$. Moreover, a minimal prime of $J$ that is not associated to $R/I$ cannot contain $I$. These are the two assertions of Fact B.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, Fact B, printed pp. 366–367, https://www.numdam.org/articles/10.24033/bsmf.2060/. A granular supporting assertion for the original Section 3 statements; definitions are unchanged.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.SectionThreeSupport.component_partition_primes
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (J I : Ideal M.CoordinateRing) (hle : J ≤ I) :
    (∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I),
      ∃ p ∈ J.minimalPrimes, p ≤ q) ∧
    (∀ p ∈ J.minimalPrimes,
      p ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → ¬ I ≤ p) := by sorry
