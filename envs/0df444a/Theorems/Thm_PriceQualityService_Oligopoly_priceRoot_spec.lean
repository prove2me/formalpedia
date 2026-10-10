-- Prove2me | Theorems.Thm_PriceQualityService_Oligopoly_priceRoot_spec
-- name    : PriceQualityService.Oligopoly.priceRoot_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:19:29.310108+00:00
-- url     : https://prove2.me/theorems/f1ec4d8e-1b3c-4dc7-98cc-e1ea15f8a271
-- title:
--   The price root $\varphi_i(A)$ exists, is unique, and decreases in $A$
-- statement:
--   Let $k$ (a unit cost) and $w$ (a price-free utility) be real numbers. For every $A > 0$ the equation
--   $$
--   1 = (p - k)\Big(1 - \frac{\exp(w - p)}{A}\Big)
--   $$
--   has exactly one solution $p = \varphi(A)$ with $p > k$ and $\exp(w - p) < A$. Moreover, on $A > 0$,
--
--   1. $\varphi(A)$ is decreasing in $A$;
--   2. $\exp(w - \varphi(A))/A$ is decreasing in $A$.
--
--   The first-order condition of firm $i$'s price problem in the MNL price competition has this form with $A = 1 + \sum_j \exp(w_j - p_j)$, so $\varphi_i(A)$ is firm $i$'s candidate equilibrium price given the aggregate.
--
--   **Formalization Note** "Decreasing" is stated as strictly decreasing (`StrictAntiOn` on $(0, \infty)$): the paper's next step derives a *unique* root $A^o$ from these monotonicities, which uses strictness.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 3 (PDF p. 36), proof of Theorem 2

import Mathlib
import Definitions.Def_PriceQualityService_Oligopoly_PriceRoot

namespace PriceQualityService.Oligopoly

/-- The function `φ_i(A)` of the proof of Theorem 2 (Online Supplement p. 3). For a unit cost `k`
and a price-free utility `w`, and every aggregate `A > 0`, the price first-order condition
`1 = (p − k)(1 − exp(w − p)/A)` has exactly one solution `p = φ(A)` with `p > k` and
`exp(w − p) < A`. Moreover `φ(A)` is decreasing in `A`, and so is `exp(w − φ(A))/A`. -/
theorem priceRoot_spec (k w : ℝ) :
    (∀ A : ℝ, 0 < A →
        IsPriceRoot k w A (priceRoot k w A) ∧ ∀ p, IsPriceRoot k w A p → p = priceRoot k w A) ∧
      StrictAntiOn (priceRoot k w) (Set.Ioi 0) ∧
      StrictAntiOn (fun A => Real.exp (w - priceRoot k w A) / A) (Set.Ioi 0) := by sorry

end PriceQualityService.Oligopoly
