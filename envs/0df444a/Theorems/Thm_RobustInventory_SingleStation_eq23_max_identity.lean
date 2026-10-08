-- Prove2me | Theorems.Thm_RobustInventory_SingleStation_eq23_max_identity
-- name    : RobustInventory.SingleStation.eq23_max_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:49:07.818114+00:00
-- url     : https://prove2.me/theorems/11ea8172-a923-41c9-b224-f1ffbc604347
-- title:
--   §3.1, Eq. (23), p. 155 — $\max(h(\bar x+A), p(-\bar x+A)) = \max(hx', -px') + \frac{2ph}{p+h}A$
-- statement:
--   Let $h, p \ge 0$ with $p + h > 0$, and let $\bar x$ and $A$ be real numbers. Put $x' = \bar x - \frac{p-h}{p+h}A$. Then
--   $$\max\big(h(\bar x + A),\ p(-\bar x + A)\big) = \max\big(h x',\ -p x'\big) + \frac{2ph}{p+h}\,A.$$
--
--   Applied with $\bar x = \bar x_{k+1}$, $A = A_k$ and $x' = x'_{k+1}$ (Eq. (22)), it turns the robust per-period cost of (21) into the holding/shortage cost $R(x'_{k+1})$ of the nominal problem with the modified demand plus the constant $\frac{2ph}{p+h}A_k$. Summed over the periods this gives parts (a) and (d) of Theorem 3.2.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 155 (PDF 6), §3.1, proof of Theorem 3.2, Eq. (23)

import Mathlib

namespace RobustInventory.SingleStation

/-- §3.1, Eq. (23), p. 155: for `h, p ≥ 0` with `p + h > 0`, real `x̄`, `A`, and
`x' = x̄ - ((p - h)/(p + h)) A`,
`max(h(x̄ + A), p(-x̄ + A)) = max(h x', -p x') + (2ph/(p + h)) A`. -/
theorem eq23_max_identity (h p xbar A : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (hph : 0 < p + h) :
    max (h * (xbar + A)) (p * (-xbar + A)) =
      max (h * (xbar - (p - h) / (p + h) * A)) (-(p * (xbar - (p - h) / (p + h) * A)))
        + 2 * p * h / (p + h) * A := by sorry

end RobustInventory.SingleStation
