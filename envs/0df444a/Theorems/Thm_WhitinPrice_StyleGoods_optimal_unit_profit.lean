-- Prove2me | Theorems.Thm_WhitinPrice_StyleGoods_optimal_unit_profit
-- name    : WhitinPrice.StyleGoods.optimal_unit_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:58:27.767154+00:00
-- url     : https://prove2.me/theorems/f27217a8-50c2-49ac-8d02-dec903a89f7f
-- title:
--   Section 3, Eq. (16) — P* = ((P₀ − 3L) + √((3L − P₀)² + 16P₀L))/4 with stock x_M(P*) uniquely maximizes expected profit
-- statement:
--   Consider the style-goods model of Whitin (1955, §3): a single selling period, stock $x \ge 0$ on hand at its start, a unit profit $P$ earned on each unit sold, and a loss $L > 0$ on each unit liquidated at its close. Mean demand is linear in the unit profit, $\mu(P) = k(P - P_0)$, where $P_0 > 0$ is the unit profit at which demand falls to zero and $k < 0$ is the reciprocal of the slope of that line; demand is uniform on $[0, 2\mu(P)]$. The expected profit is
--   $$E(P, x) = \int_0^x \big[P\Pr(X \ge t) - L\Pr(X < t)\big]\,dt,$$
--   and $x_M(P) = -2kP(P_0 - P)/(P + L)$ is the equilibrium stock (12). Let
--   $$P^* = \frac{(P_0 - 3L) + \sqrt{(3L - P_0)^2 + 16P_0L}}{4}. \tag{16}$$
--   Then
--   1. $0 < P^* < P_0$;
--   2. for every unit profit $0 < P < P_0$ and every stock $x \ge 0$, $E(P, x) \le E\big(P^*, x_M(P^*)\big)$;
--   3. equality holds only at $P = P^*$ and $x = x_M(P^*)$.
--
--   So the pair $(P^*, x_M(P^*))$ is the unique joint optimum of unit profit and stock. As Whitin observes, the optimal unit profit (16) does not involve $k$: it depends only on $P_0$ and $L$, although the optimal stock and the optimal expected profit scale with $k$.
--
--   **Formalization Note** The paper's "Solving (15) gives the optimal P" is made explicit as unique global maximization of expected profit jointly over $0 < P < P_0$ and all stocks $x \ge 0$. The independence of $k$ is visible in the hypothesis fixing $P^*$, which mentions only $P_0$ and $L$. The conditions $P_0 > 0$, $L > 0$ and $k < 0$ are implicit in the paper and are explicit hypotheses.
-- source:
--   Whitin, Inventory Control and Price Theory, Management Sci. 2 (1955), p. 67, Section 3, Eqs. (14)–(16); p. 65 (select the value of P that maximizes expected profits)

import Mathlib
import Definitions.Def_WhitinPrice_StyleGoods_Model

namespace WhitinPrice.StyleGoods
theorem optimal_unit_profit (k P₀ L Pstar : ℝ) (hk : k < 0) (hL : 0 < L) (hP₀ : 0 < P₀)
    (hPstar : Pstar = ((P₀ - 3 * L) + Real.sqrt ((3 * L - P₀) ^ 2 + 16 * P₀ * L)) / 4) :
    0 < Pstar ∧ Pstar < P₀ ∧
      (∀ P x : ℝ, 0 < P → P < P₀ → 0 ≤ x →
        expectedProfit k P₀ L P x ≤ expectedProfit k P₀ L Pstar (optimalStock k P₀ L Pstar)) ∧
      (∀ P x : ℝ, 0 < P → P < P₀ → 0 ≤ x →
        expectedProfit k P₀ L P x = expectedProfit k P₀ L Pstar (optimalStock k P₀ L Pstar) →
          P = Pstar ∧ x = optimalStock k P₀ L Pstar) := by sorry
end WhitinPrice.StyleGoods
