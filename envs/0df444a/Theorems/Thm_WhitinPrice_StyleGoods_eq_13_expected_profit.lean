-- Prove2me | Theorems.Thm_WhitinPrice_StyleGoods_eq_13_expected_profit
-- name    : WhitinPrice.StyleGoods.eq_13_expected_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:57:46.134495+00:00
-- url     : https://prove2.me/theorems/703dd757-3c4d-46dd-820b-a4a9a55b27b2
-- title:
--   Section 3, Eqs. (10), (13) — for uniform demand, E(P, x) = (P + L)x²/(4k(P₀ − P)) + Px on the support of demand
-- statement:
--   In the style-goods model (Whitin 1955, §3) with $P_0$, $L > 0$, $k < 0$, mean demand $\mu(P) = k(P - P_0)$ and demand uniform on $[0, 2\mu(P)]$, let
--   $$E(P, x) = \int_0^x \big[f(t) - g(t)\big]\,dt$$
--   be the expected profit of stocking $x$ units at unit profit $P$, where $f(t) = P\Pr(X \ge t)$ and $g(t) = L\Pr(X < t)$.
--
--   For $0 < P < P_0$ and every stock $x$ with $0 \le x \le 2\mu(P)$,
--   $$E(P, x) = \frac{P + L}{4k(P_0 - P)}\,x^2 + P\,x.$$
--
--   This is the closed form of the shaded area of Whitin's Figure II for uniform demand; at fixed $P$ it is a concave quadratic in $x$ on the support of demand, and it is the expression into which the optimal stock (12) is substituted to obtain (14).
--
--   **Formalization Note** The paper states (13) at a generic upper limit $x_m$ without a range. Beyond $2\mu(P)$ the true expected profit is not given by (13) (it decreases with slope $-L$), so the Lean states (13) only for $0 \le x \le 2\mu(P)$. $E$ is defined from the demand law, not by (13).
-- source:
--   Whitin, Inventory Control and Price Theory, Management Sci. 2 (1955), p. 66, Section 3, Eqs. (10) and (13)

import Mathlib
import Definitions.Def_WhitinPrice_StyleGoods_Model

namespace WhitinPrice.StyleGoods
theorem eq_13_expected_profit (k P₀ L P x : ℝ) (hk : k < 0) (hL : 0 < L) (hP : 0 < P)
    (hPP₀ : P < P₀) (hx₀ : 0 ≤ x) (hx : x ≤ 2 * meanDemand k P₀ P) :
    expectedProfit k P₀ L P x = (P + L) / (4 * k * (P₀ - P)) * x ^ 2 + P * x := by sorry
end WhitinPrice.StyleGoods
