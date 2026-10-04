-- Prove2me | Theorems.Thm_SeatInventory_Gaussian_protection_level_eq_mean_add
-- name    : SeatInventory.Gaussian.protection_level_eq_mean_add
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:01:46.175724+00:00
-- url     : https://prove2.me/theorems/f1ffc8c2-9a68-428e-b1a8-952ed407839c
-- title:
--   Eq. (6.11)–(6.12) — S = r̄ + Zσ̂
-- statement:
--   Let class-1 requests be $N(\bar r, \hat\sigma^2)$ with $\hat\sigma > 0$, and fares $0 < f_2 < f_1$. If $S$ solves the protection-level equation $P[r_1 \ge S] = f_2/f_1$ (Eq. (6.10)) and $Z$ solves the standard normal equation $P[N(0,1) \ge Z] = f_2/f_1$, then
--   $$S = \bar r + Z\hat\sigma \qquad \text{(Eq. (6.12))},$$
--   equivalently $Z = (S - \bar r)/\hat\sigma$ (Eq. (6.11)).
--
--   This reduces every Gaussian protection level to a single quantile of the standard normal law, and is the formula on which the book's sensitivity analysis of Sect. 6.2 is based.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, pp. 153-154, Eq. (6.10)-(6.12)

import Mathlib
import Definitions.Def_SeatInventory_Gaussian_Model

open MeasureTheory ProbabilityTheory

namespace SeatInventory.Gaussian

/-- Belobaba (1987), Eq. (6.11)–(6.12), p. 154: the protection level `S` solving (6.10) for
`N(r̄, σ̂²)` and the standardized value `Z` with `P[N(0,1) ≥ Z] = f₂ / f₁` satisfy
`S = r̄ + Z σ̂`. -/
theorem protection_level_eq_mean_add (rbar σ f₁ f₂ S Z : ℝ) (hσ : 0 < σ) (hf₂ : 0 < f₂)
    (hf : f₂ < f₁) (hS : IsProtectionLevel rbar σ f₁ f₂ S) (hZ : IsStdNormalLevel f₁ f₂ Z) :
    S = rbar + Z * σ := by sorry

end SeatInventory.Gaussian
