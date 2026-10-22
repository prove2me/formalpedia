-- Prove2me | Theorems.Thm_SpecActionsProb_Latency_expected_hits
-- name    : SpecActionsProb.Latency.expected_hits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:33.374408+00:00
-- url     : https://prove2.me/theorems/b9b40c8c-01d4-4764-9cb5-26ebc5d87bfd
-- title:
--   Appendix A — expectation of the hit count
-- statement:
--   Let $H_{t,n}$ count hits in $n$ potential windows starting at $t$. A hit skips the immediately following window. If $p(k)=1-(1-p)^k$, then $\mathbb E[H_{t,n}]=S_n$ for every start $t$, where
--
--   $$S_0=0,\quad S_1=p(k),\quad S_n=p(k)(1+S_{n-2})+(1-p(k))S_{n-1}\quad(n\ge2).$$
--
--   This connects the random hit count with the paper's recursively defined sequence.
--
--   **Formalization Note** The paper starts at its first window; stationarity permits every starting window. Windows are zero indexed, and a hit is determined by the $k$ independent branch indicators.
-- source:
--   Ye et al., Speculative Actions: A Lossless Framework for Faster Agentic Systems, arXiv:2510.04371v2, p. 14, Appendix A, 'Expected number of hits'

import Mathlib
import Definitions.Def_SpecActionsProb_Latency_Model

set_option autoImplicit false

namespace SpecActionsProb.Latency

open MeasureTheory ProbabilityTheory

/-- Appendix A, Expected number of hits, p. 14. The stationary model allows any starting window. -/
theorem expected_hits {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (α β p : ℝ) (hβ : 0 < β) (hβα : β < α) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (X : Idx k → Ω → ℝ) (hX : IsSpecModel P k α β p X) :
    ∀ t n : ℕ, (∫ ω, hitsBy X ω t n ∂P) = SpecActions.hits (SpecActions.phit k p) n := by sorry

end SpecActionsProb.Latency
