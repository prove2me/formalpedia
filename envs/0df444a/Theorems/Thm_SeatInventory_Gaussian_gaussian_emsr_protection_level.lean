-- Prove2me | Theorems.Thm_SeatInventory_Gaussian_gaussian_emsr_protection_level
-- name    : SeatInventory.Gaussian.gaussian_emsr_protection_level
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:02:01.023086+00:00
-- url     : https://prove2.me/theorems/4440a291-c109-4d85-88a8-693ce487491a
-- title:
--   Eq. (6.10)–(6.14) — Gaussian EMSR protection level S = r̄ + Zσ̂ and its sensitivity
-- statement:
--   Let class-1 requests be Gaussian, $r_1 \sim N(\bar r, \hat\sigma^2)$ with $\hat\sigma > 0$, and let the fares satisfy $0 < f_2 < f_1$. Then:
--
--   1. the protection-level equation $P[r_1 \ge S] = f_2/f_1$ (Eq. (6.10)) has exactly one real solution $S$, and the equation $P[N(0,1) \ge Z] = f_2/f_1$ has exactly one real solution $Z$;
--   2. these solutions satisfy
--   $$S = \bar r + Z\hat\sigma \qquad \text{(Eq. (6.12))};$$
--   3. $Z < 0$ if $f_2/f_1 > 1/2$, $Z > 0$ if $f_2/f_1 < 1/2$, and $Z = 0$ if $f_2/f_1 = 1/2$ (Eq. (6.14));
--   4. if $f_2/f_1 = 1/2$, then $S = \bar r$;
--   5. for every $\hat\sigma' > \hat\sigma$, the protection level $S'$ solving (6.10) for $N(\bar r, \hat\sigma'^2)$ satisfies $S' < S$ if $f_2/f_1 > 1/2$, $S' > S$ if $f_2/f_1 < 1/2$, and $S' = S$ if $f_2/f_1 = 1/2$.
--
--   This is the capstone of Sect. 6.2: the Gaussian protection level is a linear function of the mean and the standard deviation of class-1 demand, and the direction in which demand uncertainty moves it is decided by whether the discount fare is above or below half the full fare.
--
--   **Formalization Note** The protection level and $Z$ are defined only through their tail equations; the formula $S = \bar r + Z\hat\sigma$ is part of the conclusion. Seat levels are real numbers, as in the book's continuous Gaussian model.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, pp. 153-154, Eq. (6.10)-(6.12), Eq. (6.14) and the sigma-sensitivity paragraph

import Mathlib
import Definitions.Def_SeatInventory_Gaussian_Model

open MeasureTheory ProbabilityTheory

namespace SeatInventory.Gaussian

/-- Belobaba (1987), Eq. (6.10)–(6.12) and (6.14) with the σ̂-sensitivity claim, pp. 153–154.
For Gaussian class-1 requests `N(r̄, σ̂²)` with `σ̂ > 0` and fares `0 < f₂ < f₁`:
(a) (6.10) has exactly one solution `S`, the tail equation of `N(0,1)` has exactly one
solution `Z`, and `S = r̄ + Z σ̂`; (b) the sign of `Z` follows (6.14), and `S = r̄` when
`f₂ / f₁ = 1/2`; (c) for `σ̂' > σ̂` the protection level falls, rises or stays put according as
`f₂ / f₁` is above, below or equal to `1/2`. -/
theorem gaussian_emsr_protection_level (rbar σ f₁ f₂ : ℝ) (hσ : 0 < σ) (hf₂ : 0 < f₂)
    (hf : f₂ < f₁) :
    (∃! S : ℝ, IsProtectionLevel rbar σ f₁ f₂ S) ∧
    (∃! Z : ℝ, IsStdNormalLevel f₁ f₂ Z) ∧
    (∀ S Z : ℝ, IsProtectionLevel rbar σ f₁ f₂ S → IsStdNormalLevel f₁ f₂ Z →
      S = rbar + Z * σ) ∧
    (∀ Z : ℝ, IsStdNormalLevel f₁ f₂ Z →
      (1 / 2 < f₂ / f₁ → Z < 0) ∧ (f₂ / f₁ < 1 / 2 → 0 < Z) ∧ (f₂ / f₁ = 1 / 2 → Z = 0)) ∧
    (f₂ / f₁ = 1 / 2 → ∀ S : ℝ, IsProtectionLevel rbar σ f₁ f₂ S → S = rbar) ∧
    (∀ σ' S S' : ℝ, σ < σ' → IsProtectionLevel rbar σ f₁ f₂ S →
      IsProtectionLevel rbar σ' f₁ f₂ S' →
      (1 / 2 < f₂ / f₁ → S' < S) ∧ (f₂ / f₁ < 1 / 2 → S < S') ∧
        (f₂ / f₁ = 1 / 2 → S' = S)) := by sorry

end SeatInventory.Gaussian
