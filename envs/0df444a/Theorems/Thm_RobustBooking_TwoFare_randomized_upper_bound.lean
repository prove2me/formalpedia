-- Prove2me | Theorems.Thm_RobustBooking_TwoFare_randomized_upper_bound
-- name    : RobustBooking.TwoFare.randomized_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T23:03:05.296024+00:00
-- url     : https://prove2.me/theorems/e1e86a26-d0eb-46cd-84c9-51a10bd2363e
-- title:
--   Proposition 3 — no randomized booking policy beats b(r), even on the two instances I₁ and I₂
-- statement:
--   Consider the continuous two-fare booking problem with capacity $n > 0$ and fares $f_1 > f_2 > 0$, $r = f_2/f_1$. Let $(\Omega, \mu)$ be a probability space and $A(\omega)$ a deterministic online policy for each $\omega$, such that $\omega \mapsto R(A(\omega), I)$ is measurable for every instance $I$. Then
--
--   1. the randomized policy's competitive ratio is at most $b(r)$:
--   $$\inf_{I : v^*(I) > 0} \frac{\mathbb{E}_\mu[R(A, I)]}{v^*(I)} \le b(r) = \frac{1}{2-r};$$
--   2. this holds even when the instances are restricted to $I_1$ and $I_2$:
--   $$\min\left\{ \frac{\mathbb{E}_\mu[R(A, I_1)]}{R^*(I_1)},\ \frac{\mathbb{E}_\mu[R(A, I_2)]}{R^*(I_2)} \right\} \le b(r).$$
--
--   Deterministic policies are the case of a Dirac measure $\mu$. Here $I_1$ is a low-fare request for $n$ followed by a high-fare request for $n$, $I_2$ a low-fare request for $n$ alone, and $R^*$ the optimal offline revenue.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, pp. 953–954, Proposition 3

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Booking
import Definitions.Def_RobustBooking_TwoFare_BookingPolicies

open MeasureTheory

namespace RobustBooking.TwoFare

/-- Proposition 3 (Ball–Queyranne 2009, pp. 953–954). For the continuous two-fare problem with fares
`f₁ > f₂ > 0` and capacity `n > 0`, every randomized booking policy (a random choice `A ω` of a
deterministic policy, `ω ∼ μ`) has competitive ratio at most `b(r) = 1 / (2 - r)`, and this holds even
on the two instances `I₁`, `I₂` alone: the smaller of `E[R(A, I₁)] / R*(I₁)` and
`E[R(A, I₂)] / R*(I₂)` is at most `b(r)`. -/
theorem randomized_upper_bound (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → DetPolicy) (hA : ∀ I : List Request, Measurable fun ω => revenue f₁ f₂ n (A ω) I) :
    randCompetitiveRatio f₁ f₂ n μ A ≤ b (f₂ / f₁) ∧
    min ((∫ ω, revenue f₁ f₂ n (A ω) (instI1 n hn) ∂μ) / optRevenue f₁ f₂ n (instI1 n hn))
        ((∫ ω, revenue f₁ f₂ n (A ω) (instI2 n hn) ∂μ) / optRevenue f₁ f₂ n (instI2 n hn))
      ≤ b (f₂ / f₁) := by sorry

end RobustBooking.TwoFare
