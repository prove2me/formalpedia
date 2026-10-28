-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_trace_coherence_axioms
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.trace_coherence_axioms
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:24:35.665463+00:00
-- url     : https://prove2.me/theorems/57442859-b098-4afb-ac31-42fab38b2897
-- title:
--   Trace-norm-induced coherence
-- statement:
--   In every positive finite dimension,
--   $$C_{\rm tr}(\rho)=\min_{\delta\ {\rm diagonal}}\|\rho-\delta\|_{\rm tr}$$
--   has an attained minimum. It is nonnegative, zero exactly on diagonal density matrices, monotone under nonselective incoherent operations and convex on finite ensembles. Here $\|\cdot\|_{\rm tr}$ is the full trace norm, without a factor one half. This supplies (C1'), (C2a), (C3) and makes no (C2b) claim.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, Appendix H (H.3), PDF p. 11. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

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
































































/-- PDF p.11, (H.3): full trace norm, without a half factor or a selective claim. -/
theorem trace_coherence_axioms :
    DistanceAttainment fullTraceDistance ∧
    CoherenceNonnegative (fun d => distanceCandidate (fullTraceDistance d)) ∧
    CoherenceFaithful (fun d => distanceCandidate (fullTraceDistance d)) ∧
    CoherenceMonotone (fun d => distanceCandidate (fullTraceDistance d)) ∧
    CoherenceConvex (fun d => distanceCandidate (fullTraceDistance d)) := by sorry


end QAlgorithms.Papers.Independent.Independent1.P04
