-- Prove2me | Theorems.Thm_RobustBooking_BidPrice_theorem6_grid_bound
-- name    : RobustBooking.BidPrice.theorem6_grid_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:07:47.851979+00:00
-- url     : https://prove2.me/theorems/bb7c2be6-1ffa-4ed0-995a-39d72b0749f4
-- title:
--   Proof of Theorem 6, first display — on the m-fare grid (13) no policy has competitive ratio above 1/(m − (m − 1) r^(1/(m−1)))
-- statement:
--   Let $0 < f_{\min} < f_{\max}$, $n > 0$, $r = f_{\min}/f_{\max}$ and $m \ge 2$, and let $F_m = \{f_i^{(m)} = f_{\max}\, r^{(i-1)/(m-1)} : i = 1, \dots, m\}$ be the fares of Eq. (13). On the instances whose fares all lie in $F_m$, every deterministic online policy $A$, and every randomized policy (a random choice $A(\omega)$ of deterministic policies whose revenue on each such instance is measurable in $\omega$), has competitive ratio
--   $$\mathrm{CR}_{F_m} \le c^{(m)} = \frac{1}{m - (m-1)\, r^{1/(m-1)}}.$$
--
--   This is Theorem 4 of §2.1 (no policy for the continuous $m$-fare problem beats $1/\Delta$, $\Delta = m - \sum_{i=2}^m f_i/f_{i-1}$) for the geometric fares of Eq. (13), for which $f_i/f_{i-1} = r^{1/(m-1)}$. It is the first step of the proof of Theorem 6.
--
--   **Formalization Note.** Theorem 4 belongs to a concurrent draft mission of this series; it is restated here for the grid only. The competitive ratios are the `sInf`s over admissible instances with positive offline optimum, and the powers are `Real.rpow`.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 959, §2.2, proof of Theorem 6 (first display; Theorem 4 of p. 957 on the fares of Eq. (13))

import Mathlib
import Definitions.Def_RobustBooking_BidPrice_Model
import Definitions.Def_RobustBooking_BidPrice_Policy
import Definitions.Def_RobustBooking_BidPrice_Controls

namespace RobustBooking.BidPrice

open MeasureTheory

/-- First display of the proof of Theorem 6 (Ball–Queyranne 2009, §2.2, p. 959): Theorem 4 applied
to the `m`-fare problem with the fares `f_i^(m) = f_max r^((i - 1)/(m - 1))` of Eq. (13),
`r = f_min / f_max`. For `m ≥ 2`, on the instances whose fares are all among the `f_i^(m)`, no
booking policy, deterministic or randomized (a random choice `A ω`, `ω ∼ μ`, of deterministic
policies whose revenue on each admissible instance is measurable), has a competitive ratio larger than
`c^(m) = 1 / (m - (m - 1) r^(1/(m - 1)))`. -/
theorem theorem6_grid_bound (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) (m : ℕ) (hm : 2 ≤ m) :
    (∀ P : DetPolicy, competitiveRatioOn (gridFares fmin fmax m) n P ≤
        1 / ((m : ℝ) - ((m : ℝ) - 1) * discountRatio fmin fmax ^ (1 / ((m : ℝ) - 1)))) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : Ω → DetPolicy),
        (∀ I : List Request, FaresIn (gridFares fmin fmax m) I →
          Measurable fun ω => revenue n (A ω) I) →
          competitiveRatioRandOn (gridFares fmin fmax m) n μ A ≤
            1 / ((m : ℝ) - ((m : ℝ) - 1) * discountRatio fmin fmax ^ (1 / ((m : ℝ) - 1))) := by sorry

end RobustBooking.BidPrice
