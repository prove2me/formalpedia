-- Prove2me | Theorems.Thm_WhitinPrice_StyleGoods_eq_14_optimal_expected_profit
-- name    : WhitinPrice.StyleGoods.eq_14_optimal_expected_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:57:53.075991+00:00
-- url     : https://prove2.me/theorems/88dc3898-ac3d-4df9-b3e0-3fbaab51b257
-- title:
--   Section 3, Eq. (14) — at the optimal stock, E(P, x_M(P)) = −kP²(P₀ − P)/(P + L)
-- statement:
--   In the style-goods model (Whitin 1955, §3) with $P_0$, $L > 0$, $k < 0$, mean demand $\mu(P) = k(P - P_0)$ and demand uniform on $[0, 2\mu(P)]$, let $E(P, x)$ be the expected profit of stocking $x$ units at unit profit $P$ and $x_M(P) = -2kP(P_0 - P)/(P + L)$ the equilibrium stock (12). For every $0 < P < P_0$,
--   $$E\big(P, x_M(P)\big) = -\frac{kP^2(P_0 - P)}{P + L}.$$
--
--   This is the maximal expected profit attainable at unit profit $P$, as a function of $P$ alone; maximizing it over $P$ is the pricing problem whose stationary condition is the quadratic (15).
--
--   **Formalization Note** Because $k < 0$, the right-hand side is positive on $0 < P < P_0$.
-- source:
--   Whitin, Inventory Control and Price Theory, Management Sci. 2 (1955), p. 67, Section 3, Eq. (14)

import Mathlib
import Definitions.Def_WhitinPrice_StyleGoods_Model

namespace WhitinPrice.StyleGoods
theorem eq_14_optimal_expected_profit (k P₀ L P : ℝ) (hk : k < 0) (hL : 0 < L) (hP : 0 < P)
    (hPP₀ : P < P₀) :
    expectedProfit k P₀ L P (optimalStock k P₀ L P) = -(k * P ^ 2 * (P₀ - P)) / (P + L) := by sorry
end WhitinPrice.StyleGoods
