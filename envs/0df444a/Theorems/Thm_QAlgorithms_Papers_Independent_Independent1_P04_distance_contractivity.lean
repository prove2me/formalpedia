-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_distance_contractivity
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.distance_contractivity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:24:34.283035+00:00
-- url     : https://prove2.me/theorems/494994ca-03ae-4503-9467-fbc67db48dd5
-- title:
--   Contractive distances induce nonselective monotonicity
-- statement:
--   Let $D$ be a dimension-indexed nonnegative distance on density matrices whose incoherent-state minima are attained. Assume $D(\Phi(\rho),\Phi(\sigma))\le D(\rho,\sigma)$ for every completely positive trace-preserving map, including changes of finite positive dimension. For any complete incoherent Kraus family of common output dimension,
--   $$C_D\left(\sum_aK_a\rho K_a^\dagger\right)\le C_D(\rho),\qquad C_D(\rho)=\min_{\delta\ {\rm diagonal}}D(\rho,\delta).$$
--   This gives axiom (C2a) for the induced candidate.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, Distance measures (6), PDF p. 3. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

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




















































/-- PDF p.3, (6): contractivity under every CPTP map implies (C2a). -/
theorem distance_contractivity (D : (d : ℕ) → CoherenceMatrix d → CoherenceMatrix d → ℝ)
    (hD : DistanceMinimumDomain D) (hattain : DistanceAttainment D)
    (hcontract : DistanceContractive D) :
    CoherenceMonotone (fun d => distanceCandidate (D d)) := by sorry














end QAlgorithms.Papers.Independent.Independent1.P04
