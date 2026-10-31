-- Prove2me | Theorems.Thm_RobustBooking_BidPrice_theorem6_upper_bound
-- name    : RobustBooking.BidPrice.theorem6_upper_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:07:42.805501+00:00
-- url     : https://prove2.me/theorems/89a3d3c8-3556-4044-8e1d-47f28766f648
-- title:
--   Theorem 6 — no bid-price booking policy, deterministic or randomized, has competitive ratio larger than 1/(1 − ln r)
-- statement:
--   Let $0 < f_{\min} < f_{\max}$, $r = f_{\min}/f_{\max}$, and capacity $n > 0$. For the bid-price control problem, whose instances have every fare in $[f_{\min}, f_{\max}]$, every deterministic online policy $A$ satisfies
--   $$\mathrm{CR}_{[f_{\min}, f_{\max}]}(A) \le \frac{1}{1 - \ln r},$$
--   and so does every randomized policy, a random choice $A(\omega)$, $\omega \sim \mu$, of deterministic policies whose revenue on each admissible instance is measurable in $\omega$.
--
--   Together with Theorem 7 this shows that $1/(1 - \ln r)$ is the best competitive ratio achievable for the continuous bid-price problem.
--
--   **Formalization Note.** Competitive ratios are `sInf`s over admissible instances with positive offline optimum; the randomized value is the Bochner integral of the revenue, which is bounded by $n f_{\max}$ and, under the measurability hypothesis, integrable. The randomization is an arbitrary probability space, not a finitely supported distribution.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 959, Theorem 6

import Mathlib
import Definitions.Def_RobustBooking_BidPrice_Model
import Definitions.Def_RobustBooking_BidPrice_Policy
import Definitions.Def_RobustBooking_BidPrice_Controls

namespace RobustBooking.BidPrice

open MeasureTheory

/-- Theorem 6 (Ball–Queyranne 2009, p. 959). For the bid-price control problem with fare limits
`f_max` and `f_min = r f_max` (`0 < f_min < f_max`, instances with every fare in
`[f_min, f_max]`) and capacity `n > 0`, no booking policy, deterministic or randomized (a random
choice `A ω`, `ω ∼ μ`, of deterministic policies whose revenue on each admissible instance is
measurable), has a competitive ratio larger than `1 / (1 - ln r)`. -/
theorem theorem6_upper_bound (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) :
    (∀ P : DetPolicy, competitiveRatioOn (Set.Icc fmin fmax) n P ≤
        1 / (1 - Real.log (discountRatio fmin fmax))) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : Ω → DetPolicy),
        (∀ I : List Request, FaresIn (Set.Icc fmin fmax) I →
          Measurable fun ω => revenue n (A ω) I) →
          competitiveRatioRandOn (Set.Icc fmin fmax) n μ A ≤
            1 / (1 - Real.log (discountRatio fmin fmax)) := by sorry

end RobustBooking.BidPrice
