-- Prove2me | Theorems.Thm_RobustInventory_SingleStation_eq22_modified_stock
-- name    : RobustInventory.SingleStation.eq22_modified_stock
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:32:01.542658+00:00
-- url     : https://prove2.me/theorems/180fd428-73dd-4b3a-a7a1-a2e25e558e01
-- title:
--   §3.1, Eq. (22), p. 155 — the modified stock is $x'_{k+1} = \bar x_{k+1} - \frac{p-h}{p+h}A_k$
-- statement:
--   In the single-station model, let $w'$ be the modified demand (20) and, for an order sequence $u$, let $x'$ be the **modified stock** of (22): $x'_0 = x_0$ and $x'_{k+1} = x'_k + u_k - w'_k$. Then for every $k$
--   $$x'_{k+1} = \bar x_{k+1} - \frac{p-h}{p+h}\,A_k,\qquad \bar x_{k+1} = x_0 + \sum_{i=0}^{k}(u_i - \bar w_i).$$
--
--   This identifies the stock of the nominal problem with demand $w'$ with the shifted nominal stock that appears in the max identity (23).
--
--   **Formalization Note** $x'_{k+1}$ is the stock at the end of period $k$ for the demand sequence $w'$, `stock wmod u k`. The identity uses the convention $A_{-1} = 0$.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 155 (PDF 6), §3.1, proof of Theorem 3.2, Eq. (22)

import Definitions.Def_RobustInventory_SingleStation_Deviation

namespace RobustInventory.SingleStation

/-- §3.1, Eq. (22), p. 155: the modified stock `x'_{k+1}`, defined by `x'_0 = x₀` and
`x'_{k+1} = x'_k + u_k - w'_k` with the modified demand `w'` of (20), equals
`x̄_{k+1} - ((p - h)/(p + h)) A_k`. -/
theorem eq22_modified_stock (M : Model) (u : ℕ → ℝ) (k : ℕ) :
    M.stock M.wmod u k = M.xbar u k - (M.p - M.h) / (M.p + M.h) * M.A k := by sorry

end RobustInventory.SingleStation
