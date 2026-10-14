-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_8_s3_net_ext
-- name    : PersistClust.Count.theorem_4_8_s3_net_ext
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T15:57:58.03763+00:00
-- url     : https://prove2.me/theorems/2d90ddd3-c729-49ee-9e7c-c6bff649ec0a
-- title:
--   Theorem 4.8 shell — S3 (external netting): the corrected root's exact RHS form
-- statement:
--   The netting step of the Theorem 4.8 shell in its EXTERNAL-cover form — the exact RHS of the corrected Theorem 4.8. For a c-Lipschitz density f on a metric measure space, the sampleMeasure of the event that n i.i.d. samples fail to be a delta/4-geodesic-sample of the c*delta-superlevel set is at most (the coveringNumber of the superlevel set at radius delta/8 — the minimal EXTERNAL cover, centers anywhere in X) times expBound (n * (3/4) * c * delta) * (minBallMeasure at radius delta/8 over the WHOLE space, Set.univ). This is the repaired form of the paper's Lemma 4.3 at (alpha, epsilon) = (c*delta, delta/4): Lemma 4.3's as-stated pairing — external covering number with the superlevel-CENTERED ball-volume infimum — is FALSE (machine-verified on this platform; same-radius ball volumes on curved manifolds are not uniform, the lollipop obstruction), and the paper's own remedy (p.18, case b: the Bishop-Gunter uniform ball-volume lower bound) replaces the centered infimum by the global one. The proof: a fixed delta/8-ball centred at any point of X that MEETS the superlevel set still carries the Lipschitz mass lower bound (via a witness point in the intersection and the two-hop triangle delta/8 + delta/8 = delta/4, f varies by at most c*delta/4 across the ball, so f >= 3/4*c*delta on it), and the GLOBAL minBallMeasure bounds every such ball regardless of center — exactly the step that repairs Lemma 4.3's false external ball-volume claim. Per-ball miss probabilities (1-t)^n <= expBound (n * (3/4) * c * delta) V, filtered cover, finite-union bound. The degenerate top case: coveringNumber = top forces the superlevel set nonempty, which pins V < top (the ball at a superlevel point has law-mass at least (3/4)c*delta * V <= 1), so expBound is positive and the RHS is top.
-- source:
--   Formalization of the netting/covering step in the proof of Theorem 4.8, Persistence-Based Clustering in Riemannian Manifolds (rr/6968), in the repaired external-cover form (the one-token repair of Lemma 4.3's falsified external ball-volume step, per the paper's own p.18 case-b remedy hint). Child of the corrected root theorem_4_8_corrected (id 6b9ad4c5-ed11-4695-b810-2a1269327d27) whose RHS this lemma establishes verbatim; sibling of the accepted shell lemmas theorem_4_8_s1_pos_null (id e1665ca1), theorem_4_8_s2_tau_null (id 4557009e), and theorem_4_8_s3_net_int (id 17846507).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm

open MeasureTheory Bundle
open scoped ContDiff Manifold ENNReal

namespace PersistClust.Count

theorem theorem_4_8_s3_net_ext {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (f : X → ℝ) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (n : ℕ)
    (hLip : ∀ x y, |f x - f y| ≤ c * dist x y) (hdens : IsDensity μ f) :
    sampleMeasure μ n f
        {pts : Fin n → X | ¬ IsGeodesicSample (Set.range pts) (superlevel f (c * δ)) (δ / 4)}
      ≤ (coveringNumber (δ / 8) (superlevel f (c * δ)) : ENNReal)
        * expBound (n * (3 / 4 * c * δ))
            (minBallMeasure μ (δ / 8) (Set.univ : Set X))
    := by sorry
