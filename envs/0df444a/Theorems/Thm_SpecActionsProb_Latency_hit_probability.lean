-- Prove2me | Theorems.Thm_SpecActionsProb_Latency_hit_probability
-- name    : SpecActionsProb.Latency.hit_probability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:23.895982+00:00
-- url     : https://prove2.me/theorems/acd45fd7-2ab3-47dd-95ef-fd06d68a20fa
-- title:
--   Proposition 1 — probability that one of k branches hits
-- statement:
--   At any speculation window, each of the $k$ independent branches predicts the correct next call with probability $p$. The probability that at least one branch succeeds is
--
--   $$p(k)=1-(1-p)^k.$$
--
--   This identifies the hit parameter used by the paper's hit-count recurrence. For $k=0$ the hit event is empty and $p(0)=0$.
--
--   **Formalization Note** The hit event is the existence of a correct branch among `Fin k`, not a separate Bernoulli coin. Windows use zero-based indices and follow Appendix A's timing model.
-- source:
--   Ye et al., Speculative Actions: A Lossless Framework for Faster Agentic Systems, arXiv:2510.04371v2, p. 5, Proposition 1, final sentence

import Mathlib
import Definitions.Def_SpecActionsProb_Latency_Model

set_option autoImplicit false

namespace SpecActionsProb.Latency

open MeasureTheory ProbabilityTheory

/-- Proposition 1, p. 5: at least one of the independent branches predicts correctly. -/
theorem hit_probability {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (α β p : ℝ) (hβ : 0 < β) (hβα : β < α) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (X : Idx k → Ω → ℝ) (hX : IsSpecModel P k α β p X) :
    ∀ t : ℕ, P.real {ω | hitAt X t ω} = SpecActions.phit k p := by sorry

end SpecActionsProb.Latency
