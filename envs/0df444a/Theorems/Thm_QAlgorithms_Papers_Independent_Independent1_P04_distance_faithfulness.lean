-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_distance_faithfulness
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.distance_faithfulness
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:23:28.653788+00:00
-- url     : https://prove2.me/theorems/1fb24293-c038-43ff-a9c3-ab75d4659207
-- title:
--   Faithfulness of an attained distance minimum
-- statement:
--   Let $D_d$ be nonnegative on pairs of density matrices in each positive finite dimension, zero exactly on equal arguments. Suppose its minimum over incoherent density matrices is attained for every state. Define $C_D$ by the infimum of these distances. It is an actual attained minimum: a minimizing incoherent $\delta_*$ exists, $C_D(\rho)=D(\rho,\delta_*)$, and this value is no larger than $D(\rho,\delta)$ for any incoherent $\delta$. Moreover,
--   $$C_D(\rho)\ge0,\qquad C_D(\rho)=0\ \Longleftrightarrow\ \rho\text{ is diagonal}.$$
--   The attainment premise makes the source's minimum domain explicit without imposing continuity.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, Distance measures (5), (C1’), PDF p. 3. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

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



















































/-- PDF p.3, (5), (C1'): separating nonnegative distances with attained incoherent minima. -/
theorem distance_faithfulness (D : (d : ℕ) → CoherenceMatrix d → CoherenceMatrix d → ℝ)
    (hD : DistanceMinimumDomain D) (hattain : DistanceAttainment D)
    (hsep : ∀ d, 0 < d → ∀ rho sigma, IsDensityMatrix rho → IsDensityMatrix sigma →
      (D d rho sigma = 0 ↔ rho = sigma)) :
    CoherenceNonnegative (fun d => distanceCandidate (D d)) ∧
    CoherenceFaithful (fun d => distanceCandidate (D d)) ∧
    ∀ d, 0 < d → ∀ rho, IsDensityMatrix rho → AttainedCandidateSpec (D d) rho := by sorry















end QAlgorithms.Papers.Independent.Independent1.P04
