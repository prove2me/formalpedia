-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_8_corrected
-- name    : PersistClust.Count.theorem_4_8_corrected
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T14:27:19.552322+00:00
-- url     : https://prove2.me/theorems/6b9ad4c5-ed11-4695-b810-2a1269327d27
-- title:
--   Theorem 4.8 (corrected): sample-clustering consistency under tau-genericity
-- statement:
--   Corrected form of Theorem 4.8 (persistence-based clustering in Riemannian manifolds), with the frozen statement's two defects repaired. (1) The frozen RHS pairs the external covering number of the c*delta-superlevel set with the F-centred minBallMeasure over the same superlevel set - the exact pairing shown false by the five accepted disproofs of Lemma 4.3 (a ball centred in F need not meet F); this form keeps the coveringNumber factor verbatim and replaces the minBallMeasure factor by minBallMeasure mu (delta/8) univ, the smallest ball measure anywhere in X, which is what the paper's netting argument actually proves. (2) The frozen statement implicitly assumes the sample avoids the tau-level set; that fails for plateau densities (f equal to tau on a positive-measure set makes the sample hit {f = tau} with positive probability, so the event is not null in general); this form takes mu {x | f x = tau} = 0 as an explicit hypothesis (tau-genericity). Under these repairs the conclusion holds: the sampleMeasure of the event that the delta-tau cluster count of the sample fails to equal the prominent count of the diagram at d2 is at most coveringNumber (delta/8) F * expBound (n * (3/4) * c * delta) (minBallMeasure mu (delta/8) univ).
-- source:
--   Corrected form of Theorem 4.8, 'Persistence-Based Clustering in Riemannian Manifolds' (rr/6968). The frozen theorem_4_8 (id 8f14d99e-9520-4f95-a91a-167ff27ea090) is false as stated (ball-centring pairing falsified via Lemma 4.3's five accepted disproofs; tau-genericity fails on plateau densities). Sibling of the accepted deterministic core theorem_4_8_core (id 027bdb99) and the accepted shell lemma theorem_4_8_s1_pos_null (id e1665ca1).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm

open MeasureTheory Bundle
open scoped ContDiff Manifold

namespace PersistClust.Count

theorem theorem_4_8_corrected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {X : Type*} [MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [RiemannianBundle (fun x : X ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : X ↦ TangentSpace I x)]
    [IsRiemannianManifold I X] [MeasurableSpace X] [BorelSpace X]
    (hconv : 0 < convexityRadius X)
    (f : X → ℝ) (c : ℝ) (hc : 0 < c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (hdens : IsDensity (μH[(Module.finrank ℝ E : ℝ)] : Measure X) f) (htame : IsTame0 f)
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hd : d₁ < d₂) (hsep : IsSeparated (diagram0 f) d₁ d₂)
    (δ : ℝ) (hδ : 0 < δ) (hδρ : ENNReal.ofReal δ < convexityRadius X)
    (hδc : δ < (d₂ - d₁) / (5 * c))
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ) (hτnull : (μH[(Module.finrank ℝ E : ℝ)] : Measure X) {x : X | f x = τ} = 0) (n : ℕ) :
    sampleMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) n f
        {pts | ¬ ∀ σ : Fin n ≃ Fin n, IsSortOrder (f ∘ pts) σ →
          (numClusters (f ∘ pts) (fun i j => dist (pts i) (pts j)) δ τ σ : ℕ∞)
            = prominentCount (diagram0 f) d₂}
      ≤ (coveringNumber (δ / 8) (superlevel f (c * δ)) : ENNReal)
        * expBound (n * (3 / 4 * c * δ))
            (minBallMeasure (μH[(Module.finrank ℝ E : ℝ)] : Measure X) (δ / 8)
              (Set.univ : Set X)) := by sorry

end PersistClust.Count
