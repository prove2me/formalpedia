-- Prove2me | Theorems.Thm_QueueingFundamentals_MG1_busy_period_lst
-- name    : QueueingFundamentals.MG1.busy_period_lst
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T09:39:29.340723+00:00
-- url     : https://prove2.me/theorems/4b2cc7d2-1cd7-4d1f-9e41-21923833df47
-- title:
--   Eq. (5.37) — the functional equation G*(s) = B*[s + λ − λG*(s)] for the busy period
-- statement:
--   Let $\lambda > 0$, let $B$ be a service-time distribution on $[0,\infty)$ with finite mean and $\rho = \lambda\,\mathrm E[S] < 1$, and let $G$ be a probability distribution on $[0,\infty)$ satisfying the busy-period equation (5.36). Then for every real $s \ge 0$
--
--   $$
--   G^*(s) = B^*[s + \lambda - \lambda G^*(s)] .
--   $$
--
--   This functional equation (Takács's equation) determines the transform of the M/G/1 busy period and hence all its moments.
--
--   **Formalization Note** $\rho < 1$ is the standing assumption of §5.1 (p.220).
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.239–240, Eqs. (5.36)–(5.37)

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain
import Definitions.Def_QueueingFundamentals_MG1_transforms

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- Eq. (5.37), p.240: if `ρ = λ E[S] < 1` and the busy-period distribution `G`, a probability
distribution on `[0, ∞)`, satisfies (5.36), then its Laplace–Stieltjes transform satisfies
`G*(s) = B*[s + λ - λ G*(s)]` for every real `s ≥ 0`. -/
theorem busy_period_lst (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) (hρ : utilization lam B < 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hG : G (Set.Iio 0) = 0)
    (hGeq : IsBusyPeriodEquation lam B G) :
    ∀ s : ℝ, 0 ≤ s → lst G s = lst B ((s : ℂ) + lam - lam * lst G s) := by sorry

end QueueingFundamentals.MG1
