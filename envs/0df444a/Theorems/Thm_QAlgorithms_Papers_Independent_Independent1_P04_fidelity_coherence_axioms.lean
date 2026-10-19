-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_fidelity_coherence_axioms
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.fidelity_coherence_axioms
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:24:55.359865+00:00
-- url     : https://prove2.me/theorems/48518c8e-6c08-4167-8125-9b65933949ce
-- title:
--   Fidelity-induced coherence
-- statement:
--   Let $\sqrt{F(\rho,\delta)}=\operatorname{Tr}\sqrt{\sqrt\rho\,\delta\sqrt\rho}$. In every positive finite dimension the minimum
--   $$C_F(\rho)=\min_{\delta\ {\rm diagonal}}\left(1-\sqrt{F(\rho,\delta)}\right)$$
--   is attained. This candidate is nonnegative, vanishes exactly on diagonal states, is monotone under nonselective incoherent operations and is convex on finite ensembles. This establishes (C1'), (C2a), (C3); no selective monotonicity is claimed.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, Appendix H (H.1)–(H.2), PDF p. 11. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

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































































/-- PDF p.11, (H.1)–(H.2): 1 minus root fidelity satisfies (C1'), (C2a), (C3). -/
theorem fidelity_coherence_axioms :
    DistanceAttainment fidelityDistance ∧
    CoherenceNonnegative (fun d => distanceCandidate (fidelityDistance d)) ∧
    CoherenceFaithful (fun d => distanceCandidate (fidelityDistance d)) ∧
    CoherenceMonotone (fun d => distanceCandidate (fidelityDistance d)) ∧
    CoherenceConvex (fun d => distanceCandidate (fidelityDistance d)) := by sorry



end QAlgorithms.Papers.Independent.Independent1.P04
