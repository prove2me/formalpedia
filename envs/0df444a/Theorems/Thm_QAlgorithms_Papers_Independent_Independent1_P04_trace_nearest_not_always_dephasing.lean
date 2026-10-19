-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_trace_nearest_not_always_dephasing
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.trace_nearest_not_always_dephasing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:24:55.621876+00:00
-- url     : https://prove2.me/theorems/b1084deb-24ad-4146-a5e4-f7ce291fff4f
-- title:
--   Dephasing need not minimize trace distance
-- statement:
--   There exist a positive finite dimension $d$, a density matrix $\rho$ and an incoherent density matrix $\delta$ such that
--   $$\|\rho-\delta\|_{\rm tr}<\|\rho-\Delta\rho\|_{\rm tr}.$$
--   Thus dephasing need not yield a closest incoherent state for the full trace norm. Since dephasing itself is feasible, this is equivalent to the source's existential failure of equality with the minimum.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, Appendix H, last sentence, PDF p. 11. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

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

































































/-- PDF p.11, last sentence: dephasing is not always a nearest trace-norm incoherent state. -/
theorem trace_nearest_not_always_dephasing :
    ∃ d : ℕ, 0 < d ∧ ∃ rho : CoherenceMatrix d, IsDensityMatrix rho ∧
      ∃ delta : CoherenceMatrix d, IncoherentState delta ∧
        fullTraceDistance d rho delta < fullTraceDistance d rho (dephasedMatrix rho) := by sorry

end QAlgorithms.Papers.Independent.Independent1.P04
