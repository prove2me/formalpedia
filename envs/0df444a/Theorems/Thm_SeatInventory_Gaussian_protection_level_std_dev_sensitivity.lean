-- Prove2me | Theorems.Thm_SeatInventory_Gaussian_protection_level_std_dev_sensitivity
-- name    : SeatInventory.Gaussian.protection_level_std_dev_sensitivity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:02:12.208613+00:00
-- url     : https://prove2.me/theorems/068e5501-1342-4afe-9d10-de08cc0f3f94
-- title:
--   Sect. 6.2, p. 154 — effect of σ̂ on the protection level
-- statement:
--   Fix a mean $\bar r$ and fares $0 < f_2 < f_1$, and let $0 < \hat\sigma < \hat\sigma'$. Let $S$ and $S'$ be the protection levels solving $P[r_1 \ge S] = f_2/f_1$ (Eq. (6.10)) for class-1 demand $N(\bar r,\hat\sigma^2)$ and $N(\bar r,\hat\sigma'^2)$ respectively. Then
--
--   1. if $f_2/f_1 > 1/2$ (so $Z < 0$), then $S' < S$: a higher standard deviation reduces the protection level;
--   2. if $f_2/f_1 < 1/2$ (so $Z > 0$), then $S < S'$;
--   3. if $f_2/f_1 = 1/2$, then $S' = S$.
--
--   This is the book's σ̂-sensitivity claim, illustrated in its Figures 6.1 and 6.2(a).
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 154, last two paragraphs; Figure 6.1, p. 155

import Mathlib
import Definitions.Def_SeatInventory_Gaussian_Model

open MeasureTheory ProbabilityTheory

namespace SeatInventory.Gaussian

/-- Belobaba (1987), Sect. 6.2, p. 154: with `r̄` and the fares fixed, raising the standard
deviation from `σ̂` to `σ̂' > σ̂` lowers the protection level solving (6.10) when
`f₂ / f₁ > 1/2`, raises it when `f₂ / f₁ < 1/2`, and leaves it unchanged when `f₂ / f₁ = 1/2`. -/
theorem protection_level_std_dev_sensitivity (rbar σ σ' f₁ f₂ S S' : ℝ) (hσ : 0 < σ)
    (hσσ' : σ < σ') (hf₂ : 0 < f₂) (hf : f₂ < f₁) (hS : IsProtectionLevel rbar σ f₁ f₂ S)
    (hS' : IsProtectionLevel rbar σ' f₁ f₂ S') :
    (1 / 2 < f₂ / f₁ → S' < S) ∧ (f₂ / f₁ < 1 / 2 → S < S') ∧ (f₂ / f₁ = 1 / 2 → S' = S) := by sorry

end SeatInventory.Gaussian
