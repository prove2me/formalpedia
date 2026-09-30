-- Prove2me | Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_component_partition_cut
-- name    : PhilipponMultiplicity.SectionThreeSupport.component_partition_cut
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T02:39:15.953141+00:00
-- url     : https://prove2.me/theorems/cba27212-8e0f-42a9-b9a0-8e14aee1d7fb
-- title:
--   Fact C — radical of a cut and retention of isolated primes
-- statement:
--   For $J\subseteq I$, partition the actual isolated primary components of $J$ according to whether their primes are associated to $R/I$. Let $N_1$ and $N_2$ be the discarded and retained intersections. For every $P\in I$, $$\sqrt{J+(P)}=\sqrt{N_1+(P)}\cap\sqrt{N_2}.$$ Every retained minimal prime of $J$ remains minimal over $J+(P)$.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, Fact C, printed p. 367, https://www.numdam.org/articles/10.24033/bsmf.2060/. A granular supporting assertion for the original Section 3 statements; definitions are unchanged.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.SectionThreeSupport.component_partition_cut
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (J I : Ideal M.CoordinateRing) (hle : J ≤ I)
    (P : M.CoordinateRing) (hP : P ∈ I) :
    (J ⊔ Ideal.span {P}).radical =
      (discardedPart M J I ⊔ Ideal.span {P}).radical ⊓ (retainedPart M J I).radical ∧
    ∀ q ∈ J.minimalPrimes,
      q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      q ∈ (J ⊔ Ideal.span {P}).minimalPrimes := by sorry
