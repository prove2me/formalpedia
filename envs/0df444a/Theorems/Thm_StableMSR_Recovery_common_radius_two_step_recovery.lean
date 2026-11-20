-- Prove2me | Theorems.Thm_StableMSR_Recovery_common_radius_two_step_recovery
-- name    : StableMSR.Recovery.common_radius_two_step_recovery
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-19T21:33:09.356174+00:00
-- url     : https://prove2.me/theorems/d1894a83-748a-4b61-93b1-579513a7f431
-- title:
--   A single input distance recovers stable clusters by paths of at most two edges
-- statement:
--   If the stability factor satisfies γ > 1 and (γ−1)² ≥ γ, two points belong to the same cluster exactly when they are joined by a path of two edges at a common threshold. The threshold is an actual input distance, and may be taken as the largest optimal radius. This holds for all k, including 1 and n.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Lemmas 3.2 and 3.3 (intercluster and optimal-center separation). The common threshold follows by combining the two estimates. https://arxiv.org/abs/2611.03547

import Definitions.Def_StableMSR_Recovery_Geometry
open StableMSR.Recovery

theorem StableMSR.Recovery.common_radius_two_step_recovery {n : ℕ}
    (d : Point n → Point n → ℝ) (hd : IsMetricArray d) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n)
    (γ : ℝ) (hγ : 1 < γ) (hgap : γ ≤ (γ-1)^2) (O : Partition n) (hO : Stable d k γ O) :
    ∃ u v : Point n, ∀ x y : Point n,
      (∃ C ∈ O, x ∈ C ∧ y ∈ C) ↔ ∃ z : Point n, d x z ≤ d u v ∧ d z y ≤ d u v := by
  sorry
