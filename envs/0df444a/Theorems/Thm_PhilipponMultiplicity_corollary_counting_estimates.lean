-- Prove2me | Theorems.Thm_PhilipponMultiplicity_corollary_counting_estimates
-- name    : PhilipponMultiplicity.corollary_counting_estimates
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T21:11:55.808751+00:00
-- url     : https://prove2.me/theorems/2faded0c-fd06-4510-bfb6-f5f113dfcc22
-- title:
--   Section 2 — counting and mixed-degree comparisons
-- statement:
--   **Compiled open theorem statement; proof not yet supplied.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   The numerical and geometric comparisons in the corollary proofs: binomial lower bound, real-grid coset count from the quotient rank, mixed-degree lower bound, and a uniform degree-ratio estimate for disjoint factors.
-- source:
--   1986, pp.360–361. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem corollary_counting_estimates
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) :
    (∀ (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G) (T : ℕ),
      (((T + 1 : ℕ) : ℝ) ^ analyticCodimension A H.carrier) /
          (Nat.factorial (analyticCodimension A H.carrier) : ℝ) ≤
        (Nat.choose (T + analyticCodimension A H.carrier)
          (analyticCodimension A H.carrier) : ℝ)) ∧
    (∀ (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G),
      ¬ A.carrier ⊆ H.carrier →
      ∀ (m : ℕ) (γ : Fin m → G.Point) (S : ℝ), 0 ≤ S →
        S ^ samplingQuotientRank γ H ≤
          (((fun x => translate x H.carrier) '' samplingGrid γ S).ncard : ℝ)) ∧
    (∀ (H : AlgebraicSubgroup G) (r : SourceMixedCodimensionIndex G H)
        (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
      (mixedDegree G H.carrier r.complementIndex : ℝ) *
        (Nat.factorial (varietyDimension G H.carrier) : ℝ) /
        (∏ i, (Nat.factorial (r.complementIndex i) : ℝ)) *
        (∏ i, (D i : ℝ) ^ r.complementIndex i) ≤ hilbertDegreeForm G H.carrier D) ∧
    (HasDisjointFactors G → ∃ c : ℝ, 0 < c ∧
      ∀ (H : AlgebraicSubgroup G) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
        0 < hilbertDegreeForm G H.carrier D ∧
        hilbertDegreeForm G Set.univ D / hilbertDegreeForm G H.carrier D ≤
          c * ∏ i, (D i : ℝ) ^ factorCodimension G H i) := by sorry

end PhilipponMultiplicity
