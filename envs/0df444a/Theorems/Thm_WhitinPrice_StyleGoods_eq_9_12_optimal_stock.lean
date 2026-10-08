-- Prove2me | Theorems.Thm_WhitinPrice_StyleGoods_eq_9_12_optimal_stock
-- name    : WhitinPrice.StyleGoods.eq_9_12_optimal_stock
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:01:10.967394+00:00
-- url     : https://prove2.me/theorems/c8d6c8ff-501c-4661-b618-565b23d674d0
-- title:
--   Section 3, Eqs. (9), (12) — x_M = −2kP(P₀ − P)/(P + L) is the unique root of f = g and the unique optimal stock
-- statement:
--   In the style-goods model (Whitin 1955, §3) with $P_0$, $L > 0$, $k < 0$, mean demand $\mu(P) = k(P - P_0)$, demand uniform on $[0, 2\mu(P)]$, marginal curves $f, g$ and expected profit $E(P, x) = \int_0^x [f - g]$, fix a unit profit $0 < P < P_0$ and let
--   $$x_M = -\frac{2kP(P_0 - P)}{P + L}.$$
--   Then:
--   1. $0 < x_M < 2\mu(P)$, so the equilibrium stock lies strictly inside the support of demand;
--   2. for every stock $x \ge 0$, the equilibrium condition (9), $f(x) - g(x) = 0$, holds if and only if $x = x_M$;
--   3. $x_M$ maximizes expected profit over all stocks: $E(P, x) \le E(P, x_M)$ for every $x \ge 0$;
--   4. the maximizer is unique: if $x \ge 0$ and $E(P, x) = E(P, x_M)$, then $x = x_M$.
--
--   This is the optimal inventory level for a given unit profit, the point $Q$ below the intersection of $f$ and $g$ in Whitin's Figure II; substituting it into the expected profit yields (14).
--
--   **Formalization Note** The paper says "Equation (9) may be solved for $x$" and calls the solution the equilibrium (optimal) value; the Lean makes the uniqueness of the root and the global optimality over all stocks $x \ge 0$, including stocks beyond the support of demand, explicit.
-- source:
--   Whitin, Inventory Control and Price Theory, Management Sci. 2 (1955), p. 66, Section 3, Eqs. (9) and (12); p. 65 (optimality of OQ)

import Mathlib
import Definitions.Def_WhitinPrice_StyleGoods_Model

namespace WhitinPrice.StyleGoods
theorem eq_9_12_optimal_stock (k P₀ L P : ℝ) (hk : k < 0) (hL : 0 < L) (hP : 0 < P)
    (hPP₀ : P < P₀) :
    0 < optimalStock k P₀ L P ∧ optimalStock k P₀ L P < 2 * meanDemand k P₀ P ∧
      (∀ x : ℝ, 0 ≤ x →
        (marginalProfit k P₀ P x - marginalLoss k P₀ L P x = 0 ↔ x = optimalStock k P₀ L P)) ∧
      (∀ x : ℝ, 0 ≤ x → expectedProfit k P₀ L P x ≤ expectedProfit k P₀ L P (optimalStock k P₀ L P)) ∧
      (∀ x : ℝ, 0 ≤ x →
        expectedProfit k P₀ L P x = expectedProfit k P₀ L P (optimalStock k P₀ L P) →
          x = optimalStock k P₀ L P) := by sorry
end WhitinPrice.StyleGoods
