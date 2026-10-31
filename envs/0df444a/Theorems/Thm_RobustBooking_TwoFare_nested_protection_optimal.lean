-- Prove2me | Theorems.Thm_RobustBooking_TwoFare_nested_protection_optimal
-- name    : RobustBooking.TwoFare.nested_protection_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T23:03:54.076009+00:00
-- url     : https://prove2.me/theorems/4e6a53a9-023c-4d45-9eef-bf36ea6f574d
-- title:
--   Theorem 1 — the nested two-fare protection level (1 − b(r))n is b(r)-competitive, and b(r) is best possible
-- statement:
--   Consider the continuous two-fare booking problem: capacity $n > 0$ (real), fares $f_1 > f_2 > 0$, discount ratio $r = f_2/f_1 \in (0,1)$, requests arriving online with positive real quantities that may be partially accepted, irrevocable decisions. Let $b(r) = 1/(2-r)$ (Eq. (1)). Then:
--
--   1. the nested booking policy with protection level $\theta_1 = (1-b(r))\,n$ (low-fare booking limit $b(r)\,n$) has competitive ratio exactly $b(r)$;
--   2. every deterministic online booking policy has competitive ratio at most $b(r)$;
--   3. every randomized online booking policy — a random choice $A(\omega)$, $\omega \sim \mu$, of deterministic policies with $\omega \mapsto R(A(\omega), I)$ measurable for each instance $I$ — has competitive ratio at most $b(r)$:
--   $$\inf_{I : v^*(I) > 0} \frac{\mathbb{E}_\mu[R(A, I)]}{v^*(I)} \le \frac{1}{2-r}.$$
--
--   So the nested policy is best possible among all online booking policies, deterministic or randomized, and the optimal competitive ratio of the continuous two-fare problem is $1/(2-r)$.
--
--   **Formalization Note.** The competitive ratio is the infimum over instances with positive offline optimum; the randomized ratio uses the Bochner integral, which is well defined because revenue is bounded by $f_1 n$ and measurable by hypothesis. Clause 2 is the Dirac case of clause 3 and is stated separately for readability.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 954, Theorem 1

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Booking
import Definitions.Def_RobustBooking_TwoFare_BookingPolicies

open MeasureTheory

namespace RobustBooking.TwoFare

/-- Theorem 1 (Ball–Queyranne 2009, p. 954). For the continuous two-fare booking problem with
fares `f₁ > f₂ > 0` (discount ratio `r = f₂ / f₁ ∈ (0, 1)`) and capacity `n > 0`, the nested policy
with protection level `θ₁ = (1 - b(r)) n` has competitive ratio exactly `b(r) = 1 / (2 - r)`, and no
online booking policy, deterministic or randomized, has a larger competitive ratio. -/
theorem nested_protection_optimal (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n) :
    competitiveRatio f₁ f₂ n (nested n ((1 - b (f₂ / f₁)) * n)) = b (f₂ / f₁) ∧
    (∀ A : DetPolicy, competitiveRatio f₁ f₂ n A ≤ b (f₂ / f₁)) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (A : Ω → DetPolicy), (∀ I : List Request, Measurable fun ω => revenue f₁ f₂ n (A ω) I) →
      randCompetitiveRatio f₁ f₂ n μ A ≤ b (f₂ / f₁)) := by sorry

end RobustBooking.TwoFare
