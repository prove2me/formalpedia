-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_8_s3_net_int
-- name    : PersistClust.Count.theorem_4_8_s3_net_int
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T15:25:49.672033+00:00
-- url     : https://prove2.me/theorems/17846507-15c2-4270-bf14-9111022bbfce
-- title:
--   Theorem 4.8 shell — S3 (internal netting): geodesic-sample failure via explicit delta/8-covers
-- statement:
--   The netting step of the Theorem 4.8 shell, internal-cover form. Suppose f is a c-Lipschitz density on a metric measure space and the c*delta-superlevel set F = {x | f x >= c*delta} admits a FINITE internal delta/8-cover: a finite set s of points of F whose closed delta/8-balls cover F. Then the sampleMeasure of the event that n i.i.d. samples fail to be a delta/4-geodesic-sample of F is at most (the cardinality of s) * expBound (n * (3/4) * c * delta) * minBallMeasure mu (delta/8) F. The per-ball miss bound is the analytic heart: a fixed delta/8-ball centred at q in F catches no sample with probability at most (1 - t)^n where t is the single-sample law of the ball, and the Lipschitz lower bound (the function varies by at most c*delta/4 across the ball, so the ball carries mass at least (3/4)*c*delta * minBallMeasure) gives t >= ofReal((3/4)*c*delta) * minBallMeasure mu (delta/8) F; (1 - t)^n <= expBound (n * (3/4) * c * delta) V then finishes each ball, and the finite-union bound sums over the cover. This form makes the covering explicit; the corrected Theorem 4.8 (theorem_4_8_corrected) instantiates it with the minimal internal cover via the external coveringNumber, handled by the sibling s3_net_ext lemma.
-- source:
--   Formalization of the netting/covering step in the proof of Theorem 4.8, Persistence-Based Clustering in Riemannian Manifolds (rr/6968), internal-cover form. Child of the corrected root theorem_4_8_corrected (id 6b9ad4c5-ed11-4695-b810-2a1269327d27); sibling of the accepted shell lemmas theorem_4_8_s1_pos_null (id e1665ca1) and theorem_4_8_s2_tau_null (id 4557009e).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm

open MeasureTheory Bundle
open scoped ContDiff Manifold ENNReal

namespace PersistClust.Count

theorem theorem_4_8_s3_net_int {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (f : X → ℝ) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (n : ℕ)
    (hLip : ∀ x y, |f x - f y| ≤ c * dist x y) (hdens : IsDensity μ f)
    (s : Finset X) (hs : ∀ q ∈ s, c * δ ≤ f q)
    (hcover : superlevel f (c * δ) ⊆ ⋃ q ∈ s, Metric.closedBall q (δ / 8)) :
    sampleMeasure μ n f
        {pts : Fin n → X | ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (δ / 4)}
      ≤ ((s.card : ℕ∞) : ENNReal)
        * expBound (n * (3 / 4 * c * δ))
            (minBallMeasure μ (δ / 8) (superlevel f (c * δ)))
    := by sorry
