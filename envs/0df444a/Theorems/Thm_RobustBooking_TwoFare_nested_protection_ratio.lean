-- Prove2me | Theorems.Thm_RobustBooking_TwoFare_nested_protection_ratio
-- name    : RobustBooking.TwoFare.nested_protection_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T23:02:43.241725+00:00
-- url     : https://prove2.me/theorems/c2f7d11f-e216-4b19-9f75-4288657b9bb5
-- title:
--   Proposition 1 — the nested policy with protection level (1 − b(r))n has competitive ratio b(r)
-- statement:
--   Consider the continuous two-fare booking problem with capacity $n > 0$ and fares $f_1 > f_2 > 0$, and let $r = f_2/f_1 \in (0,1)$ be the discount ratio. Let $A$ be the nested protection-level policy with protection level
--   $$\theta_1 = (1 - b(r))\,n, \qquad b(r) = \frac{1}{2-r},$$
--   that is, with low-fare booking limit $n - \theta_1 = b(r)\,n$. Then the competitive ratio of $A$ equals $b(r)$:
--   $$\inf_{I \,:\, v^*(I) > 0} \frac{v'_A(I)}{v^*(I)} \;=\; \frac{1}{2 - r}.$$
--   This is the achievability half of Theorem 1: the nested policy guarantees at least a fraction $b(r)$ of the offline optimum on every instance, and the guarantee is attained (on $I_1$).
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 953, Proposition 1

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Booking
import Definitions.Def_RobustBooking_TwoFare_BookingPolicies

namespace RobustBooking.TwoFare

/-- Proposition 1 (Ball–Queyranne 2009, p. 953). For the continuous two-fare booking problem with
fares `f₁ > f₂ > 0` and capacity `n > 0`, the nested policy with protection level
`θ₁ = (1 - b(r)) n`, `r = f₂ / f₁`, has competitive ratio exactly `b(r) = 1 / (2 - r)`. -/
theorem nested_protection_ratio (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n) :
    competitiveRatio f₁ f₂ n (nested n ((1 - b (f₂ / f₁)) * n)) = b (f₂ / f₁) := by sorry

end RobustBooking.TwoFare
