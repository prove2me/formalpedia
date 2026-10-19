-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_distance_joint_convexity
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.distance_joint_convexity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:23:48.399985+00:00
-- url     : https://prove2.me/theorems/9b2155e5-a2c1-4145-81b8-2b0dc4797ddb
-- title:
--   Joint convexity induces convex coherence
-- statement:
--   Let $D$ be nonnegative and jointly convex on density-matrix pairs in every positive finite dimension, with attained incoherent-state minima. For any finite ensemble $(p_a,\rho_a)$, there are minimizing incoherent states $\delta_a^*$, and
--   $$C_D\left(\sum_ap_a\rho_a\right)\le D\left(\sum_ap_a\rho_a,\sum_ap_a\delta_a^*\right)\le\sum_ap_aD(\rho_a,\delta_a^*)=\sum_ap_a C_D(\rho_a).$$
--   Thus $C_D$ is convex. No contractivity assumption is needed.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, Distance measures (7), PDF p. 3. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false

/-! Quantifying Coherence, arXiv:1311.0275v3. Fixed bases and arbitrary finite dimensions.
Local predicates apply to density matrices only; invalid matrices carry no coherence guarantees. -/

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P04

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq





















































/-- PDF p.3, (7): joint convexity implies (C3), without a contractivity hypothesis. -/
theorem distance_joint_convexity (D : (d : ℕ) → CoherenceMatrix d → CoherenceMatrix d → ℝ)
    (hD : DistanceMinimumDomain D) (hattain : DistanceAttainment D)
    (hconvex : DistanceJointConvex D) :
    CoherenceConvex (fun d => distanceCandidate (D d)) ∧
    ∀ d, 0 < d → ∀ a (p : Fin a → ℝ) (rho : Fin a → CoherenceMatrix d),
      Learning.IsDistribution p → (∀ i, IsDensityMatrix (rho i)) →
      ∃ sigma : Fin a → CoherenceMatrix d,
        (∀ i, IncoherentState (sigma i) ∧
          distanceCandidate (D d) (rho i) = D d (rho i) (sigma i)) ∧
        distanceCandidate (D d) (ensembleMixture p rho) ≤
          D d (ensembleMixture p rho) (ensembleMixture p sigma) ∧
        D d (ensembleMixture p rho) (ensembleMixture p sigma) ≤
          (∑ i, p i * D d (rho i) (sigma i)) ∧
        (∑ i, p i * D d (rho i) (sigma i)) =
          ∑ i, p i * distanceCandidate (D d) (rho i) := by sorry













end QAlgorithms.Papers.Independent.Independent1.P04
