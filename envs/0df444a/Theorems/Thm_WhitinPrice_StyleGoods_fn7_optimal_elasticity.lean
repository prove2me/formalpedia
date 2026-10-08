-- Prove2me | Theorems.Thm_WhitinPrice_StyleGoods_fn7_optimal_elasticity
-- name    : WhitinPrice.StyleGoods.fn7_optimal_elasticity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:58:01.268088+00:00
-- url     : https://prove2.me/theorems/02508707-d8f1-472f-aa4a-7ae5906cbddd
-- title:
--   Section 3, footnote 7 — the optimal elasticity is P*/(P₀ − P*) and tends to 1 as P₀ becomes large relative to L
-- statement:
--   In the style-goods model (Whitin 1955, §3), mean demand is $\mu(P) = k(P - P_0)$ with $k < 0$, $P_0 > 0$, and the liquidation loss is $L > 0$. Let $P^* = \big((P_0 - 3L) + \sqrt{(3L - P_0)^2 + 16P_0L}\big)/4$ be the optimal unit profit (16). Then:
--   1. the elasticity of mean demand with respect to unit profit at $P^*$ is
--   $$-\mu'(P^*)\,\frac{P^*}{\mu(P^*)} = \frac{P^*}{P_0 - P^*};$$
--   2. with $L$ fixed, writing $P^*(P_0)$ for (16) as a function of $P_0$,
--   $$\lim_{P_0 \to \infty} \frac{P^*(P_0)}{P_0 - P^*(P_0)} = 1.$$
--
--   The second item is Whitin's remark that "as $P_0$ becomes large relative to $L$, the optimal elasticity approaches unity".
--
--   **Formalization Note** Elasticity is taken with the sign convention that makes it positive for a downward-sloping demand line. "$P_0$ large relative to $L$" is read as $P_0 \to \infty$ with $L > 0$ fixed; since $P^*$ is homogeneous of degree one in $(P_0, L)$, this is the same as $P_0/L \to \infty$.
-- source:
--   Whitin, Inventory Control and Price Theory, Management Sci. 2 (1955), p. 67, Section 3, footnote 7

import Mathlib
import Definitions.Def_WhitinPrice_StyleGoods_Model

open Filter Topology

namespace WhitinPrice.StyleGoods
theorem fn7_optimal_elasticity (k P₀ L Pstar : ℝ) (hk : k < 0) (hL : 0 < L) (hP₀ : 0 < P₀)
    (hPstar : Pstar = ((P₀ - 3 * L) + Real.sqrt ((3 * L - P₀) ^ 2 + 16 * P₀ * L)) / 4) :
    -(deriv (fun Q : ℝ => meanDemand k P₀ Q) Pstar) * Pstar / meanDemand k P₀ Pstar
        = Pstar / (P₀ - Pstar) ∧
      Tendsto (fun R : ℝ =>
          (((R - 3 * L) + Real.sqrt ((3 * L - R) ^ 2 + 16 * R * L)) / 4) /
            (R - ((R - 3 * L) + Real.sqrt ((3 * L - R) ^ 2 + 16 * R * L)) / 4))
        atTop (𝓝 1) := by sorry
end WhitinPrice.StyleGoods
