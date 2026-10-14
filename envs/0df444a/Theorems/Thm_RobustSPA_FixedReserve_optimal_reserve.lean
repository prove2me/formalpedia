-- Prove2me | Theorems.Thm_RobustSPA_FixedReserve_optimal_reserve
-- name    : RobustSPA.FixedReserve.optimal_reserve
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:54.808216+00:00
-- url     : https://prove2.me/theorems/3b81ca0f-d36f-4917-9318-11823aa5a53d
-- title:
--   Proof of Proposition 5, p. App-11 — the closed-form worst-case regret is minimized over r ∈ [0,1] exactly at r* = 1/(n+1), with value (n/(n+1))ⁿ
-- statement:
--   Let $n\ge 1$ and let $W_n(r)$ be the closed form of Proposition 5: $W_1(r)=\max(1-r,r)$ and, for $n\ge2$, $W_n(r)=\frac{(1-r)^n(n-1)^{n-1}}{((1-r)n-r)^{n-1}}$ for $r\le\frac12$ and $W_n(r)=r$ for $r>\frac12$. Then
--   $$\min_{r\in[0,1]} W_n(r)=W_n\Big(\frac1{n+1}\Big)=\Big(\frac{n}{n+1}\Big)^n,$$
--   and $r^*=\frac1{n+1}$ is the only minimizer in $[0,1]$.
--
--   This is the "optimal reserve" part of Proposition 5: among second-price auctions with a fixed reserve, the reserve $1/(n+1)$ minimizes the worst-case regret.
--
--   **Formalization Note** The page says the exponent is "maximized at $r^*=1/(n+1)$"; the derivative it computes changes sign from negative to positive there, so $r^*$ is the minimizer, as the proposition itself states. Reserves are restricted to $[0,1]$, the support of the valuations.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. App-11, Proof of Proposition 5 (optimal reserve)

import Mathlib
import Definitions.Def_RobustSPA_FixedReserve_Setting

open MeasureTheory

namespace RobustSPA.FixedReserve

/-- Proof of Proposition 5, p. App-11: over reserves `r ∈ [0,1]`, the closed-form worst-case
regret `wcFixed n r` is minimized exactly at `r* = 1/(n+1)`, with value `(n/(n+1))ⁿ`. -/
theorem optimal_reserve (n : ℕ) (hn : 0 < n) :
    IsLeast (wcFixed n '' Set.Icc 0 1) (((n : ℝ) / (n + 1)) ^ n) ∧
    wcFixed n (1 / (n + 1)) = ((n : ℝ) / (n + 1)) ^ n ∧
    ∀ r ∈ Set.Icc (0 : ℝ) 1, wcFixed n r = ((n : ℝ) / (n + 1)) ^ n → r = 1 / (n + 1) := by sorry

end RobustSPA.FixedReserve
