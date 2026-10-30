-- Prove2me | Theorems.Thm_SLPEPricing_Regret_round_count
-- name    : SLPEPricing.Regret.round_count
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:19.832623+00:00
-- url     : https://prove2.me/theorems/0f937394-a248-4f08-9652-2b2915798e8b
-- title:
--   p. 24, Step 2 of the proof of Theorem 1 — SLPE runs at most C + log₂(log T) rounds (repaired from natural log)
-- statement:
--   Let $0<\mu<2$ and $\rho>0$. Consider the round schedule of SLPE, $\Delta_1=\tfrac12$, $\Delta_{i+1}=\mu\Delta_i^2$, $n_i=\lceil2\rho^4\log T/\Delta_i^4\rceil$, round $i$ starting at period $3\sum_{j<i}n_j$, and let $i_{\max}$ be the number of rounds that start before the horizon $T$. There is a constant $C$, depending only on $\mu$ and $\rho$, such that for every integer $T\ge3$
--   $$i_{\max}\le C+\log_2(\log T).$$
--
--   Because $\Delta_i$ shrinks doubly exponentially, only $O(\log\log T)$ rounds fit into $T$ periods; since each round charges three prices, this is what bounds the number of price changes.
--
--   **Formalization Note** The page concludes $i_{\max}\le\log(1/\log(2/\mu))+\log(\log(T/(2\mu\rho^4\log T)))$ from $2^i\le(\ldots)$, a step that needs the base-2 logarithm while every other log of the paper is natural; with natural logs the printed bound fails (at $\mu=1.9$, $\rho=1$, $T=10^6$ the schedule has 7 rounds against a bound of 5.26). The statement uses $\log_2$ of the natural $\log T$ and absorbs the paper's explicit constant and the inner $T/(2\mu\rho^4\log T)$ into $C$. $i_{\max}$ counts rounds whose start is $<T$, i.e. rounds that charge at least one period.
-- source:
--   Perakis & Singhvi, Dynamic Pricing with Unknown Non-Parametric Demand and Limited Price Changes, SSRN 3336949 (PDF of 2020-07-03), p. 24, Step 2 of the proof of Theorem 1 (bound on i_max)

import Mathlib
import Definitions.Def_SLPEPricing_Regret_Model

namespace SLPEPricing.Regret

/-- The round count (p. 24, Step 2 of the proof of Theorem 1), repaired with `log₂`. For
`0 < μ < 2` and `ρ > 0` there is a constant `C` (depending on `μ, ρ` only) such that for every
`T ≥ 3` the number of rounds of SLPE that charge a period satisfies
`i_max ≤ C + log₂(log T)`. -/
theorem round_count (μ ρ : ℝ) (hμ0 : 0 < μ) (hμ2 : μ < 2) (hρ : 0 < ρ) :
    ∃ C : ℝ, ∀ T : ℕ, 3 ≤ T → (iMax μ ρ T : ℝ) ≤ C + Real.logb 2 (Real.log (T : ℝ)) := by sorry

end SLPEPricing.Regret
