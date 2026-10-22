-- Prove2me | Theorems.Thm_SpecActionsProb_Latency_total_saving
-- name    : SpecActionsProb.Latency.total_saving
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:18.584645+00:00
-- url     : https://prove2.me/theorems/12713f2c-8c97-4d0d-b7a2-7d531c9aec07
-- title:
--   Appendix A — total expected speculative runtime
-- statement:
--   With $T\ge1$ real calls and $T-1$ potential speculation windows, let $H_{0,T-1}$ be the random hit count. For the Appendix A execution rule, the expected speculative runtime is
--
--   $$\mathbb E[T_s]=\frac{T}{\beta}-\mathbb E[H_{0,T-1}]\frac{\alpha}{\beta(\alpha+\beta)}.$$
--
--   This is the paper's total-saving identity stated for the random execution time and random hit count.
--
--   **Formalization Note** The last step opens no window. A hit costs $\min(A_t,B_t)+B_{t+1}$ and consumes the next window; windows use zero-based indices.
-- source:
--   Ye et al., Speculative Actions: A Lossless Framework for Faster Agentic Systems, arXiv:2510.04371v2, p. 15, Appendix A, 'Total saving'

import Mathlib
import Definitions.Def_SpecActionsProb_Latency_Model

set_option autoImplicit false

namespace SpecActionsProb.Latency

open MeasureTheory ProbabilityTheory

/-- Appendix A, Total saving, p. 15. -/
theorem total_saving {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (α β p : ℝ) (hβ : 0 < β) (hβα : β < α) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (X : Idx k → Ω → ℝ) (hX : IsSpecModel P k α β p X) :
    ∀ T : ℕ, 1 ≤ T →
      (∫ ω, specRuntime X T ω ∂P)
        = T / β - (∫ ω, hitsBy X ω 0 (T - 1) ∂P) * (α / (β * (α + β))) := by sorry

end SpecActionsProb.Latency
