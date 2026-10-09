-- Prove2me | Theorems.Thm_SLPricing_Resp_proposition_6
-- name    : SLPricing.Resp.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:51.031667+00:00
-- url     : https://prove2.me/theorems/776519cf-96ca-47db-8108-144b5eabeb66
-- title:
--   Proposition 6, p. 24 — with SL, responsive pricing earns more than without SL whenever $\delta_c\le\Delta_{lr}(\gamma)$ or $\delta_c\ge\Delta_{hr}(\gamma)$
-- statement:
--   Consider responsive pricing with social learning, $\gamma>0$, and fix $\sigma_p$, $\gamma$ and $c$. For a consumer discount factor $d\in[0,1]$ let $\pi_r^*(d)$ be the firm's optimal expected profit, and $\pi_r^*(d)|_{\gamma\to0}$ the optimal expected profit in the absence of social learning. Then there are thresholds
--   $$\Delta_{lr}(\gamma)\in(0,1],\qquad \Delta_{hr}(\gamma)\in[0,1)$$
--   such that for every $d\in[0,1]$ with $d\le\Delta_{lr}(\gamma)$ or $d\ge\Delta_{hr}(\gamma)$,
--   $$\pi_r^*(d)\ >\ \pi_r^*(d)|_{\gamma\to0}.$$
--
--   So when the firm adjusts its price to the reviews, social learning raises its optimal profit both for sufficiently impatient and for sufficiently patient consumers, although it also makes consumers more willing to delay.
--
--   **Formalization Note** The benchmark is the same model at $\gamma=0$. Optimal values are suprema in the extended reals over all first-period prices and all their equilibria, with the second-period price chosen optimally at every realization of the reviews. The thresholds are stated in the half-open intervals of the page; with closed intervals the statement would be trivial.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Proposition 6, p. 24 (proof p. 33)

import Mathlib
import Definitions.Def_SLPricing_Resp_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.Resp

/-- Proposition 6, p. 24 (proof p. 33): with social learning (`γ > 0`) there are thresholds
`Δlr ∈ (0, 1]` and `Δhr ∈ [0, 1)` such that for every consumer discount factor `d ∈ [0, 1]` with
`d ≤ Δlr` or `d ≥ Δhr`, the firm's optimal expected profit under responsive pricing is strictly
greater than in the absence of social learning. -/
theorem proposition_6 (P : Params) (hP : P.Standing) (hγ : 0 < P.γ) :
    ∃ Δlr ∈ Ioc (0 : ℝ) 1, ∃ Δhr ∈ Ico (0 : ℝ) 1, ∀ d ∈ Icc (0 : ℝ) 1, (d ≤ Δlr ∨ Δhr ≤ d) →
      respValue (P.withδc d).noSL < respValue (P.withδc d) := by sorry

end SLPricing.Resp
