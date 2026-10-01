-- Prove2me | Theorems.Thm_PhilipponMultiplicity_source_boundary_counterexamples
-- name    : PhilipponMultiplicity.source_boundary_counterexamples
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T21:11:59.714126+00:00
-- url     : https://prove2.me/theorems/c3ab172d-0f05-450f-a8af-88e7d02613b0
-- title:
--   Source corrections — dimension-zero and zero-degree obstructions
-- statement:
--   Require actual complex embedded groups witnessing three failures: the converse at the trivial group, the strengthened forward statement at a two-point group, and Corollary 2.2 with degree (1,0) on two additive factors. These are explicit correction targets, not assumptions supplied to the source theorems.
-- source:
--   1986, p.359; 1987, p.398; boundary audit. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Support
set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem source_boundary_counterexamples :
    (∃ (G : EmbeddedGroupProduct ℂ) (A : AnalyticSubgroup G)
        (H : AlgebraicSubgroup G),
      Subsingleton G.Point ∧ G.dimension = 0 ∧ H.carrier = Set.univ ∧
      A.carrier = {0} ∧ analyticCodimension A H.carrier = 0 ∧
      hilbertDegreeForm G Set.univ (fun _ => 1) = 1 ∧
      hilbertDegreeForm G H.carrier (fun _ => 1) = 1 ∧
      (Nat.choose (0 + analyticCodimension A H.carrier)
          (analyticCodimension A H.carrier) : ℝ) *
        (cosetCount {0} H.carrier : ℝ) * hilbertDegreeForm G H.carrier (fun _ => 1) ≤
        (1 / ((4 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ))) *
          hilbertDegreeForm G Set.univ (fun _ => 1) ∧
      ¬ ∃ P : G.CoordinateRing,
        (∀ h ∈ H.carrier, (1 : WithTop ℕ) ≤ vanishingOrder A P h) ∧
        (∃ x : G.Point, x ∉ zeroLocusOnGroup G P)) ∧
    (∃ (G : EmbeddedGroupProduct ℂ) (A : AnalyticSubgroup G)
        (sample : Finset G.Point) (P : G.CoordinateRing),
      G.dimension = 0 ∧ sample.card = 2 ∧ 0 ∈ sample ∧ A.carrier = {0} ∧
      P ≠ 0 ∧ IsMultihomogeneousOfDegree G P (fun _ => 1) ∧
      (∀ g ∈ sumset sample G.dimension, vanishingOrder A P g = ⊤) ∧
      ¬ ∃ H : AlgebraicSubgroup G,
        ∀ g ∈ sample, translate g H.carrier ⊆ zeroLocusOnGroup G P) ∧
    (∃ (G : EmbeddedGroupProduct ℂ) (A : AnalyticSubgroup G)
        (P : G.CoordinateRing),
      G.factorCount = 2 ∧ (∀ i, (G.factor i).dimension = 1) ∧
      A.dimension = 1 ∧ P ≠ 0 ∧
      IsMultihomogeneousOfDegree G P (fun i => if i.val = 0 then 1 else 0) ∧
      vanishingOrder A P 0 = 1 ∧
      (∀ c : ℝ, 0 < c → ∀ H : AlgebraicSubgroup G,
        H.IsConnected → ¬ A.carrier ⊆ H.carrier →
        ∃ r : SourceMixedCodimensionIndex G H,
          c * r.degreeMonomial (fun i => if i.val = 0 then 1 else 0) ≤
            (cosetCount {0} H.carrier : ℝ) *
              (mixedDegree G H.carrier r.complementIndex : ℝ)) ∧
      ¬ ∃ g : G.Point, translate g A.carrier ⊆ zeroLocusOnGroup G P) := by sorry

end PhilipponMultiplicity
