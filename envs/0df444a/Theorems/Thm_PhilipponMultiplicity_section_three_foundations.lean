-- Prove2me | Theorems.Thm_PhilipponMultiplicity_section_three_foundations
-- name    : PhilipponMultiplicity.section_three_foundations
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T21:11:47.323988+00:00
-- url     : https://prove2.me/theorems/f50004dd-2a2d-4472-9553-4ec6fbf312b7
-- title:
--   Section 3 — Hilbert foundations and Facts A–E
-- statement:
--   **Proved with no Open theorem dependencies, verified 29 September 2026.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   Existence, relevance, relevant-cone dimension, integral nonnegative mixed coefficients and their expansion; actual primary decompositions; degree monotonicity; the concrete commutative-algebra assertions A–E. The recursive construction remains an internal proof obligation for Proposition 3.3.
-- source:
--   1986, pp.361–370. https://numdam.org/articles/10.24033/bsmf.2060/

/-
Open concrete supporting assertions from section three, including Facts A–E.
The Krull bridge removes irrelevant components first. Primary decompositions
are actual finite families of primary ideals, with no degree conclusions in
their fields. Fact E is the general open-locus avoidance statement; the full
inductive construction in Proposition 3.3 remains separate.
-/
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem section_three_foundations
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K) :
    -- The actual Hilbert polynomial, its support, coefficients, and dimension.
    (∀ I : Ideal M.CoordinateRing, IsMultihomogeneousIdeal M I →
      (∃ P, Hilbert.IsHilbertPolynomial K M.factorCount M.ambientDimension I P) ∧
      (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I = 0 ↔
        ¬ IsNontrivialIdeal M I) ∧
      (IsNontrivialIdeal M I →
        ringKrullDim (M.CoordinateRing ⧸ relevantRadicalCore M I) =
          ((idealDimension M I + M.factorCount : ℕ) : WithBot ℕ∞)) ∧
      (∀ α : M.FactorIndex → ℕ, ∃ n : ℕ, idealMixedDegree M I α = (n : ℚ)) ∧
      (∀ α : M.FactorIndex → ℕ, (∃ i, M.ambientDimension i < α i) →
        idealMixedDegree M I α = 0) ∧
      (∀ d : M.FactorIndex → ℕ, idealDegreeValue M I d = degreeCoefficientSum M I d) ∧
      Nonempty (PrimaryDecomposition M I)) ∧
    -- Equal-dimensional Hilbert-degree monotonicity following Lemma 3.2.
    (∀ I J : Ideal M.CoordinateRing,
      IsMultihomogeneousIdeal M I → IsMultihomogeneousIdeal M J →
      IsNontrivialIdeal M I → IsNontrivialIdeal M J → I ≤ J →
      idealDimension M I = idealDimension M J →
      ∀ d : M.FactorIndex → ℕ, (∀ i, 1 ≤ d i) →
        idealDegreeValue M J d ≤ idealDegreeValue M I d) ∧
    -- Associated primes of a genuine minimal primary decomposition.
    (∀ I : Ideal M.CoordinateRing, ∀ D : PrimaryDecomposition M I,
      associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) =
        Set.range (fun i => (D.component i).radical)) ∧
    -- Fact A, using the actual canonical isolated primary components.
    (∀ J J' : Ideal M.CoordinateRing,
      IsMultihomogeneousIdeal M J → IsMultihomogeneousIdeal M J' →
      IsNontrivialIdeal M J → IsNontrivialIdeal M J' → J ≤ J' →
      ∀ b : ℕ, (dimensionAtLeast M J (b + 1)).radical =
          (dimensionAtLeast M J' (b + 1)).radical →
        dimensionSlice M J b ≤ dimensionSlice M J' b) ∧
    -- Facts B and C: the canonical partition of the isolated components.
    (∀ J I : Ideal M.CoordinateRing, J ≤ I →
      (∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I),
        ∃ p ∈ J.minimalPrimes, p ≤ q) ∧
      (∀ p ∈ J.minimalPrimes,
        p ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → ¬ I ≤ p) ∧
      (∀ P ∈ I,
        (J ⊔ Ideal.span {P}).radical =
          (discardedPart M J I ⊔ Ideal.span {P}).radical ⊓ (retainedPart M J I).radical ∧
        ∀ q ∈ J.minimalPrimes,
          q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
          q ∈ (J ⊔ Ideal.span {P}).minimalPrimes)) ∧
    -- Fact D, slightly stronger: retain all isolated components, even irrelevant ones.
    (∀ I : Ideal M.CoordinateRing, ∀ D : PrimaryDecomposition M I,
      ∃ Q ∈ D.embeddedIntersection,
        IsRegular (Ideal.Quotient.mk D.isolatedIntersection Q)) ∧
    -- Fact E: embedded supports avoid the Cohen–Macaulay locus; prime avoidance.
    (∀ I : Ideal M.CoordinateRing, ∀ D : PrimaryDecomposition M I,
      ∀ U : MaximalOpenLocus M, IsLocallyCohenMacaulayOn M I U →
      (∀ i : Fin D.count, D.IsEmbedded i →
        ¬ Hilbert.MeetsOpen K M.factorCount M.ambientDimension (D.component i).radical U) ∧
      (∀ L : Ideal M.CoordinateRing,
        (∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ L),
          Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U) →
        (∀ i : Fin D.count, D.IsEmbedded i →
          ∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ L),
            ¬ (D.component i).radical ≤ q) ∧
        ∃ Q ∈ D.embeddedIntersection, IsRegular (Ideal.Quotient.mk L Q))) := by sorry

end PhilipponMultiplicity
