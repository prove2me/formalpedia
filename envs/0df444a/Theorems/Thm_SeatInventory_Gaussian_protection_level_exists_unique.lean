-- Prove2me | Theorems.Thm_SeatInventory_Gaussian_protection_level_exists_unique
-- name    : SeatInventory.Gaussian.protection_level_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:01:02.111984+00:00
-- url     : https://prove2.me/theorems/a7ed1035-4d61-4cfb-8c40-698296aa4b9a
-- title:
--   Eq. (6.10) — the Gaussian EMSR protection level exists and is unique
-- statement:
--   Let class-1 requests be Gaussian, $r_1 \sim N(\bar r, \hat\sigma^2)$ with $\hat\sigma > 0$, and let the fares satisfy $0 < f_2 < f_1$. Then the protection-level equation
--   $$P[r_1 \ge S] = \frac{f_2}{f_1} \qquad \text{(Eq. (6.10))}$$
--   has exactly one real solution $S$.
--
--   This makes "the optimal value of $S_2^1$" of Sect. 6.2 a well-defined function of $\bar r$, $\hat\sigma$ and the fare ratio, which is what the sensitivity statements of the mission are about.
--
--   **Formalization Note** Seat levels are real numbers (the continuous Gaussian model of Sect. 6.2). The hypothesis $\hat\sigma > 0$ excludes the Dirac law, for which (6.10) has no solution.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 153, Eq. (6.10)

import Mathlib
import Definitions.Def_SeatInventory_Gaussian_Model

open MeasureTheory ProbabilityTheory

namespace SeatInventory.Gaussian

/-- Belobaba (1987), Eq. (6.10), p. 153: for Gaussian class-1 requests `N(r̄, σ̂²)` with
`σ̂ > 0` and fares `0 < f₂ < f₁`, the equation `P[r₁ ≥ S] = f₂ / f₁` has exactly one real
solution `S`. -/
theorem protection_level_exists_unique (rbar σ f₁ f₂ : ℝ) (hσ : 0 < σ) (hf₂ : 0 < f₂)
    (hf : f₂ < f₁) :
    ∃! S : ℝ, IsProtectionLevel rbar σ f₁ f₂ S := by sorry

end SeatInventory.Gaussian
