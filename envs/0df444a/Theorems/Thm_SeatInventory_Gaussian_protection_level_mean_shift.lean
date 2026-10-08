-- Prove2me | Theorems.Thm_SeatInventory_Gaussian_protection_level_mean_shift
-- name    : SeatInventory.Gaussian.protection_level_mean_shift
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:01:27.369325+00:00
-- url     : https://prove2.me/theorems/4fea4254-b5f3-43c4-86d3-c5fbca8170bb
-- title:
--   Sect. 6.2, p. 154 — a unit change in r̄ moves the protection level by one seat
-- statement:
--   Fix a standard deviation $\hat\sigma > 0$ and fares $0 < f_2 < f_1$. Let $S$ be the protection level for class-1 demand $N(\bar r, \hat\sigma^2)$ and $S'$ the protection level for $N(\bar r + c, \hat\sigma^2)$, each defined by the tail equation $P[r_1 \ge S] = f_2/f_1$ (Eq. (6.10)). Then
--   $$S' = S + c.$$
--
--   In the book's words: for a fixed $Z$ and $\hat\sigma$, each unit change in $\bar r$ results in a one-seat change in the optimal number of seats protected.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 154, the paragraph after Eq. (6.12)

import Mathlib
import Definitions.Def_SeatInventory_Gaussian_Model

open MeasureTheory ProbabilityTheory

namespace SeatInventory.Gaussian

/-- Belobaba (1987), Sect. 6.2, p. 154: with `σ̂` and the fares fixed, shifting the mean demand
`r̄` by `c` shifts the protection level solving (6.10) by exactly `c`. -/
theorem protection_level_mean_shift (rbar σ f₁ f₂ c S S' : ℝ) (hσ : 0 < σ) (hf₂ : 0 < f₂)
    (hf : f₂ < f₁) (hS : IsProtectionLevel rbar σ f₁ f₂ S)
    (hS' : IsProtectionLevel (rbar + c) σ f₁ f₂ S') :
    S' = S + c := by sorry

end SeatInventory.Gaussian
