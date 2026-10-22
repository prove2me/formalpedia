-- Prove2me | Theorems.Thm_RobustBooking_TwoFare_deterministic_upper_bound
-- name    : RobustBooking.TwoFare.deterministic_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T23:03:11.847181+00:00
-- url     : https://prove2.me/theorems/7ecb5e63-8dc8-454c-b8ab-b3c5310135c0
-- title:
--   Proposition 2 — no deterministic online booking policy has competitive ratio larger than b(r)
-- statement:
--   Consider the continuous two-fare booking problem with capacity $n > 0$ and fares $f_1 > f_2 > 0$, $r = f_2/f_1$. For every deterministic online booking policy $A$,
--   $$\inf_{I \,:\, v^*(I) > 0} \frac{v'_A(I)}{v^*(I)} \;\le\; b(r) = \frac{1}{2-r}.$$
--   Together with Proposition 1 this shows the nested policy is best possible among deterministic policies.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 953, Proposition 2

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Booking
import Definitions.Def_RobustBooking_TwoFare_BookingPolicies

namespace RobustBooking.TwoFare

/-- Proposition 2 (Ball–Queyranne 2009, p. 953). For the continuous two-fare problem with fares
`f₁ > f₂ > 0` and capacity `n > 0`, no deterministic online booking policy has a competitive
ratio larger than `b(r) = 1 / (2 - r)`, `r = f₂ / f₁`. -/
theorem deterministic_upper_bound (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n)
    (A : DetPolicy) :
    competitiveRatio f₁ f₂ n A ≤ b (f₂ / f₁) := by sorry

end RobustBooking.TwoFare
