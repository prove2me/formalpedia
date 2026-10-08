-- Prove2me | Theorems.Thm_WhitinPrice_StyleGoods_eq_11_marginal_curves
-- name    : WhitinPrice.StyleGoods.eq_11_marginal_curves
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:57:48.429464+00:00
-- url     : https://prove2.me/theorems/d7c10f9a-61cf-4b9d-b3d0-2582eeb06bd5
-- title:
--   Section 3, Eq. (11) — for uniform demand, f(x) = P x/(2k(P₀ − P)) + P and g(x) = −L x/(2k(P₀ − P))
-- statement:
--   In the style-goods model (Whitin 1955, §3), let $P_0$ be the unit profit at which demand falls to zero, $L > 0$ the unit liquidation loss, and $k < 0$ the reciprocal of the slope of the line relating unit profit and mean demand $\mu(P) = k(P - P_0)$. Fix a unit profit $P$ with $0 < P < P_0$, and let demand be uniform on $[0, 2\mu(P)]$. Let $f(x) = P\Pr(X \ge x)$ and $g(x) = L\Pr(X < x)$ be the expected marginal profit and loss of the $x$-th unit.
--
--   Then for every stock $x$ with $0 \le x \le 2\mu(P)$,
--   $$f(x) = \frac{P}{2k(P_0 - P)}\,x + P, \qquad g(x) = \frac{-L}{2k(P_0 - P)}\,x.$$
--
--   Both curves are linear on the support of demand: $f$ falls from $P$ to $0$ and $g$ rises from $0$ to $L$. These are the two lines whose intersection gives the optimal stock (12) and whose enclosed area gives the expected profit (13).
--
--   **Formalization Note** The paper writes (11) without a range; the Lean restricts to the support $0 \le x \le 2\mu(P)$, outside which $f$ and $g$ are constant. The sign $k < 0$ is implicit in the paper (positive mean demand below $P_0$) and is an explicit hypothesis.
-- source:
--   Whitin, Inventory Control and Price Theory, Management Sci. 2 (1955), p. 66, Section 3, Eq. (11)

import Mathlib
import Definitions.Def_WhitinPrice_StyleGoods_Model

namespace WhitinPrice.StyleGoods
theorem eq_11_marginal_curves (k P₀ L P x : ℝ) (hk : k < 0) (hL : 0 < L) (hP : 0 < P)
    (hPP₀ : P < P₀) (hx₀ : 0 ≤ x) (hx : x ≤ 2 * meanDemand k P₀ P) :
    marginalProfit k P₀ P x = P / (2 * k * (P₀ - P)) * x + P ∧
      marginalLoss k P₀ L P x = -L / (2 * k * (P₀ - P)) * x := by sorry
end WhitinPrice.StyleGoods
