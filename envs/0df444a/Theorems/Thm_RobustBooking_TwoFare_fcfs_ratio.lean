-- Prove2me | Theorems.Thm_RobustBooking_TwoFare_fcfs_ratio
-- name    : RobustBooking.TwoFare.fcfs_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T23:03:14.873924+00:00
-- url     : https://prove2.me/theorems/7d177b97-aed2-4b15-a142-7279e8ec5b6e
-- title:
--   Proposition 5 — first-come, first-served has competitive ratio r
-- statement:
--   Consider the continuous two-fare booking problem with capacity $n > 0$ and fares $f_1 > f_2 > 0$. The first-come, first-served policy (accept every request in full while capacity remains) has competitive ratio exactly the discount ratio:
--   $$\inf_{I : v^*(I) > 0} \frac{v'_{\mathrm{FCFS}}(I)}{v^*(I)} = r = \frac{f_2}{f_1}.$$
--   Since $r < 1/(2-r)$ for $0 < r < 1$, FCFS is strictly worse than the best nested policy.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 955, Proposition 5

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Booking
import Definitions.Def_RobustBooking_TwoFare_BookingPolicies

namespace RobustBooking.TwoFare

/-- Proposition 5 (Ball–Queyranne 2009, p. 955). For the continuous two-fare booking problem with
fares `f₁ > f₂ > 0` and capacity `n > 0`, first-come first-served has competitive ratio exactly
`r = f₂ / f₁`. -/
theorem fcfs_ratio (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n) :
    competitiveRatio f₁ f₂ n fcfs = f₂ / f₁ := by sorry

end RobustBooking.TwoFare
