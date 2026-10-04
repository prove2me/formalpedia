-- Prove2me | Theorems.Thm_SeatInventory_Gaussian_level_antitone_fare_ratio
-- name    : SeatInventory.Gaussian.level_antitone_fare_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:01:53.52633+00:00
-- url     : https://prove2.me/theorems/17021870-4b16-4c1a-8d46-4de98b481cbe
-- title:
--   Sect. 6.2, p. 157 — Z and the protection level decrease with f₂/f₁
-- statement:
--   Let $(f_1, f_2)$ and $(g_1, g_2)$ be two fare pairs with $0 < f_2 < f_1$, $0 < g_2 < g_1$ and
--   $$\frac{f_2}{f_1} < \frac{g_2}{g_1}.$$
--   Let $Z, Z'$ be the standardized levels, $P[N(0,1) \ge Z] = f_2/f_1$ and $P[N(0,1) \ge Z'] = g_2/g_1$, and for a fixed class-1 demand $N(\bar r, \hat\sigma^2)$ with $\hat\sigma > 0$ let $S, S'$ be the protection levels solving (6.10) for the two fare ratios. Then $Z' < Z$ and $S' < S$.
--
--   In the book's words: the value of $Z$ decreases with $f_2/f_1$, meaning that the closer $f_2$ is to $f_1$ proportionately, the smaller the optimal protection level.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 157, second paragraph

import Mathlib
import Definitions.Def_SeatInventory_Gaussian_Model

open MeasureTheory ProbabilityTheory

namespace SeatInventory.Gaussian

/-- Belobaba (1987), Sect. 6.2, p. 157: the standardized value `Z` decreases with the fare
ratio, and so does the protection level: if `f₂ / f₁ < g₂ / g₁` (both pairs with
`0 < lower fare < higher fare`), then `Z' < Z` and `S' < S` for the same Gaussian class-1 demand. -/
theorem level_antitone_fare_ratio (rbar σ f₁ f₂ g₁ g₂ Z Z' S S' : ℝ) (hσ : 0 < σ)
    (hf₂ : 0 < f₂) (hf : f₂ < f₁) (hg₂ : 0 < g₂) (hg : g₂ < g₁) (hlt : f₂ / f₁ < g₂ / g₁)
    (hZ : IsStdNormalLevel f₁ f₂ Z) (hZ' : IsStdNormalLevel g₁ g₂ Z')
    (hS : IsProtectionLevel rbar σ f₁ f₂ S) (hS' : IsProtectionLevel rbar σ g₁ g₂ S') :
    Z' < Z ∧ S' < S := by sorry

end SeatInventory.Gaussian
