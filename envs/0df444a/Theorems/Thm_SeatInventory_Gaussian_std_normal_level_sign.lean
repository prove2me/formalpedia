-- Prove2me | Theorems.Thm_SeatInventory_Gaussian_std_normal_level_sign
-- name    : SeatInventory.Gaussian.std_normal_level_sign
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:01:58.842624+00:00
-- url     : https://prove2.me/theorems/a9ecbfaa-64eb-4750-a25c-31d961753fa2
-- title:
--   Eq. (6.14) — the sign of Z is set by whether f₂/f₁ exceeds 1/2
-- statement:
--   Let $0 < f_2 < f_1$ and let $Z$ satisfy $P[N(0,1) \ge Z] = f_2/f_1$. Then
--
--   1. if $f_2/f_1 > 1/2$, then $Z < 0$;
--   2. if $f_2/f_1 < 1/2$, then $Z > 0$;
--   3. if $f_2/f_1 = 1/2$, then $Z = 0$;
--   4. if $f_2/f_1 = 1/2$, then for every mean $\bar r$ and every $\hat\sigma > 0$, the protection level $S$ solving $P[r_1 \ge S] = f_2/f_1$ for $r_1 \sim N(\bar r,\hat\sigma^2)$ equals $\bar r$.
--
--   Item 4 is the book's remark that at a fare ratio of one half "the optimal $S$ will simply equal $\bar r$" and varying $\hat\sigma$ has no effect.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 154, Eq. (6.14) and the sentence following it

import Mathlib
import Definitions.Def_SeatInventory_Gaussian_Model

open MeasureTheory ProbabilityTheory

namespace SeatInventory.Gaussian

/-- Belobaba (1987), Eq. (6.14), p. 154: the standardized value `Z` with
`P[N(0,1) ≥ Z] = f₂ / f₁` is negative when `f₂ / f₁ > 1/2`, positive when `f₂ / f₁ < 1/2`,
and zero when `f₂ / f₁ = 1/2`; in the last case every protection level solving (6.10) equals
`r̄`, whatever `σ̂ > 0`. -/
theorem std_normal_level_sign (f₁ f₂ Z : ℝ) (hf₂ : 0 < f₂) (hf : f₂ < f₁)
    (hZ : IsStdNormalLevel f₁ f₂ Z) :
    (1 / 2 < f₂ / f₁ → Z < 0) ∧ (f₂ / f₁ < 1 / 2 → 0 < Z) ∧ (f₂ / f₁ = 1 / 2 → Z = 0) ∧
      (f₂ / f₁ = 1 / 2 → ∀ rbar σ S : ℝ, 0 < σ → IsProtectionLevel rbar σ f₁ f₂ S → S = rbar) := by sorry

end SeatInventory.Gaussian
