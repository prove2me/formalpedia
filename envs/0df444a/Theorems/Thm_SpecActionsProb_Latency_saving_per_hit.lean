-- Prove2me | Theorems.Thm_SpecActionsProb_Latency_saving_per_hit
-- name    : SpecActionsProb.Latency.saving_per_hit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:17.9398+00:00
-- url     : https://prove2.me/theorems/31c6055d-31f4-4836-b76d-ad9ddaf424f2
-- title:
--   Appendix A — expected saving from a correct speculation
-- statement:
--   Let $A_t\sim\mathrm{Exp}(\alpha)$ be a speculator latency and $B_t\sim\mathrm{Exp}(\beta)$ an independent real-call latency. A correct speculation saves $(B_t-A_t)_+=\max(B_t-A_t,0)$, whose expectation is
--
--   $$\mathbb E[(B_t-A_t)_+]=\frac{\alpha}{\beta(\alpha+\beta)}.$$
--
--   This converts the paper's evaluated density integral into an expectation of the primitive random latencies.
--
--   **Formalization Note** The two latencies are members of the mutually independent family. The timing is Appendix A's $\min(A_t,B_t)$ block rule.
-- source:
--   Ye et al., Speculative Actions: A Lossless Framework for Faster Agentic Systems, arXiv:2510.04371v2, p. 14, Appendix A, 'Expected time saved per hit'

import Mathlib
import Definitions.Def_SpecActionsProb_Latency_Model

set_option autoImplicit false

namespace SpecActionsProb.Latency

open MeasureTheory ProbabilityTheory

/-- Appendix A, Expected time saved per hit, p. 14. -/
theorem saving_per_hit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (α β p : ℝ) (hβ : 0 < β) (hβα : β < α) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (X : Idx k → Ω → ℝ) (hX : IsSpecModel P k α β p X) :
    ∀ t : ℕ, (∫ ω, max (X (.real t) ω - X (.spec t) ω) 0 ∂P)
      = α / (β * (α + β)) := by sorry

end SpecActionsProb.Latency
