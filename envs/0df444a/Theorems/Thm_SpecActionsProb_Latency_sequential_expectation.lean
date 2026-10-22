-- Prove2me | Theorems.Thm_SpecActionsProb_Latency_sequential_expectation
-- name    : SpecActionsProb.Latency.sequential_expectation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:19.409389+00:00
-- url     : https://prove2.me/theorems/816ef690-b170-43cb-bfda-e11d4f85ce19
-- title:
--   Appendix A — expected sequential runtime
-- statement:
--   Let $B_t$ be independent real-call latencies with exponential rate $\beta>0$. For a horizon of $T$ calls, the sequential runtime is their sum and
--
--   $$\mathbb E[T_{\mathrm{seq}}]=T/\beta.$$
--
--   This supplies the denominator for the runtime ratio, including the zero-horizon identity before division.
--
--   **Formalization Note** The random runtime is the sum of the primitive call latencies. The Appendix A model indexes steps from zero.
-- source:
--   Ye et al., Speculative Actions: A Lossless Framework for Faster Agentic Systems, arXiv:2510.04371v2, p. 14, Appendix A, 'Baseline'

import Mathlib
import Definitions.Def_SpecActionsProb_Latency_Model

set_option autoImplicit false

namespace SpecActionsProb.Latency

open MeasureTheory ProbabilityTheory

/-- Appendix A, Baseline, p. 14. -/
theorem sequential_expectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (α β p : ℝ) (hβ : 0 < β) (hβα : β < α) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (X : Idx k → Ω → ℝ) (hX : IsSpecModel P k α β p X) :
    ∀ T : ℕ, (∫ ω, seqRuntime X T ω ∂P) = SpecActions.seqTime T β := by sorry

end SpecActionsProb.Latency
