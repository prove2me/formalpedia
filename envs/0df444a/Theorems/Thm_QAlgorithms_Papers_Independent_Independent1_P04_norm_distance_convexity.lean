-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_norm_distance_convexity
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.norm_distance_convexity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:23:30.090743+00:00
-- url     : https://prove2.me/theorems/6178dd3b-ff6e-487d-ab2b-f9cfc48168dc
-- title:
--   Any matrix norm induces a convex attained candidate
-- statement:
--   In each positive finite dimension choose any genuine norm on the complex vector space of matrices. It need not be unitarily invariant or contractive. For every density matrix the minimum over diagonal density matrices is attained, and the resulting candidate satisfies
--   $$C(\rho)=\min_{\delta\ {\rm diagonal}}\|\rho-\delta\|,\qquad C\left(\sum_ap_a\rho_a\right)\le\sum_ap_a C(\rho_a).$$
--   The norm is specified by nonnegativity, definiteness, the triangle inequality and complex absolute homogeneity.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, Distance measures following (7), PDF p. 3. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

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






















































/-- PDF p.3 following (7): every genuine matrix norm yields an attained convex candidate. -/
theorem norm_distance_convexity (N : (d : ℕ) → CoherenceMatrixNorm d) :
    (∀ d, 0 < d → ∀ rho, IsDensityMatrix rho →
      AttainedCandidateSpec (fun X Y => (N d).value (X-Y)) rho) ∧
    CoherenceConvex (fun d => distanceCandidate (fun X Y => (N d).value (X-Y))) := by sorry












end QAlgorithms.Papers.Independent.Independent1.P04
