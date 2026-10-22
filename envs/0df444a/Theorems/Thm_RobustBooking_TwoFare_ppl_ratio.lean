-- Prove2me | Theorems.Thm_RobustBooking_TwoFare_ppl_ratio
-- name    : RobustBooking.TwoFare.ppl_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T23:03:27.069033+00:00
-- url     : https://prove2.me/theorems/6f2ecbad-a591-484f-baab-d84e15db2b43
-- title:
--   Proposition 6 — the PPL policy with θ₁ = n/2 has competitive ratio 1/2, best possible among PPL policies
-- statement:
--   Consider the continuous two-fare booking problem with capacity $n > 0$ and fares $f_1 > f_2 > 0$. For a protection level $\theta_1 \in [0, n]$, the partitioned protection-level policy $\mathrm{PPL}_{\theta_1}$ accepts at most $\theta_1$ units of high-fare quantity and at most $\theta_2 = n - \theta_1$ units of low-fare quantity. Then
--   $$\mathrm{CR}(\mathrm{PPL}_{n/2}) = \tfrac12 \qquad\text{and}\qquad \mathrm{CR}(\mathrm{PPL}_{\theta_1}) \le \tfrac12 \ \text{ for every } \theta_1 \in [0, n],$$
--   where $\mathrm{CR}(A) = \inf_{I : v^*(I) > 0} v'_A(I)/v^*(I)$. The bound quantifies over PPL policies only, not over all online policies.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 955, Proposition 6

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Booking
import Definitions.Def_RobustBooking_TwoFare_BookingPolicies

namespace RobustBooking.TwoFare

/-- Proposition 6 (Ball–Queyranne 2009, p. 955). For the continuous two-fare booking problem with
fares `f₁ > f₂ > 0` and capacity `n > 0`, the partitioned protection-level policy with
`θ₁ = n / 2` has competitive ratio exactly `1 / 2`, and no partitioned protection-level policy
(any `θ₁ ∈ [0, n]`) has a larger competitive ratio. -/
theorem ppl_ratio (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n) :
    competitiveRatio f₁ f₂ n (ppl n (n / 2)) = 1 / 2 ∧
    ∀ θ₁ : ℝ, 0 ≤ θ₁ → θ₁ ≤ n → competitiveRatio f₁ f₂ n (ppl n θ₁) ≤ 1 / 2 := by sorry

end RobustBooking.TwoFare
