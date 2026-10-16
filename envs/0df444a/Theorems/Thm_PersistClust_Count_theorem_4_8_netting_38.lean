-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_8_netting_38
-- name    : PersistClust.Count.theorem_4_8_netting_38
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-16T05:29:44.345895+00:00
-- url     : https://prove2.me/theorems/1b019f15-0b1d-4e91-9987-b1138cc3a993
-- title:
--   Netting bound with the original 4.8 pairing: P(sample is not a geodesic 3δ/8-sample of F^{cδ}) ≤ N_{δ/8}(F^{cδ}) e^{−n(3/4)cδ V_{δ/8}(F^{cδ})}
-- statement:
--   Let μ be a measure on a metric space X with Borel σ-algebra, f a c-Lipschitz probability density for μ (c > 0), δ > 0 and n ∈ ℕ. For n i.i.d. samples from f, the probability that the sample is not a geodesic (3δ/8)-sample of the superlevel set F^{cδ} = {f ≥ cδ} is at most N_{δ/8}(F^{cδ}) · exp(−n·(3/4)cδ·V_{δ/8}(F^{cδ})), where N_{δ/8} is the external covering number (closed δ/8-balls centred anywhere) and V_{δ/8}(F^{cδ}) is the infimum of μ(B(x, δ/8)) over centres x ∈ F^{cδ} — exactly the pairing of the right-hand side of Theorem 4.8 (and Lemma 4.3) of RR-6968, with the netting radius relaxed from δ/4 to 3δ/8.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.8), for the proof of the ORIGINAL frozen statement theorem_4_8 (8f14d99e) that avoids the unjustified external-ball comparison of the paper's netting step.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting

open MeasureTheory

namespace PersistClust.Count

theorem theorem_4_8_netting_38 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (f : X → ℝ) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (n : ℕ)
    (hLip : ∀ x y, |f x - f y| ≤ c * dist x y) (hdens : IsDensity μ f) :
    sampleMeasure μ n f
        {pts : Fin n → X |
          ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (3 * δ / 8)}
      ≤ (coveringNumber (δ / 8) (superlevel f (c * δ)) : ENNReal)
        * expBound (n * (3 / 4 * c * δ))
            (minBallMeasure μ (δ / 8) (superlevel f (c * δ)))
    := by sorry
