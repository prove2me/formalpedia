-- Prove2me | Theorems.Thm_WhitinPrice_StyleGoods_eq_15_stationary_quadratic
-- name    : WhitinPrice.StyleGoods.eq_15_stationary_quadratic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:58:23.103083+00:00
-- url     : https://prove2.me/theorems/ff6e4696-ed02-4724-aa05-931208a46fce
-- title:
--   Section 3, Eq. (15) — the derivative of P ↦ E(P, x_M(P)) vanishes iff 2P² + (3L − P₀)P − 2P₀L = 0
-- statement:
--   In the style-goods model (Whitin 1955, §3) with $P_0$, $L > 0$, $k < 0$, let $V(P) = E(P, x_M(P))$ be the expected profit at unit profit $P$ when the optimal stock $x_M(P) = -2kP(P_0 - P)/(P + L)$ is held. For every $0 < P < P_0$, $V$ is differentiable at $P$ with
--   $$V'(P) = \frac{kP\,\big(2P^2 + (3L - P_0)P - 2P_0L\big)}{(P + L)^2},$$
--   and consequently
--   $$V'(P) = 0 \iff 2P^2 + (3L - P_0)P - 2P_0L = 0. \tag{15}$$
--
--   This is the first-order condition for the profit-maximizing unit profit; its positive root is (16).
--
--   **Formalization Note** The paper differentiates the closed form (14); the Lean differentiates the model function $P \mapsto E(P, x_M(P))$ itself, which agrees with (14) on $(0, P_0)$. The explicit derivative is stated, so the equivalence is not an artefact of Lean's convention that `deriv` is $0$ at non-differentiable points.
-- source:
--   Whitin, Inventory Control and Price Theory, Management Sci. 2 (1955), p. 67, Section 3, Eqs. (14) and (15)

import Mathlib
import Definitions.Def_WhitinPrice_StyleGoods_Model

namespace WhitinPrice.StyleGoods
theorem eq_15_stationary_quadratic (k P₀ L P : ℝ) (hk : k < 0) (hL : 0 < L) (hP : 0 < P)
    (hPP₀ : P < P₀) :
    HasDerivAt (fun Q : ℝ => expectedProfit k P₀ L Q (optimalStock k P₀ L Q))
        (k * P * (2 * P ^ 2 + (3 * L - P₀) * P - 2 * P₀ * L) / (P + L) ^ 2) P ∧
      (deriv (fun Q : ℝ => expectedProfit k P₀ L Q (optimalStock k P₀ L Q)) P = 0 ↔
        2 * P ^ 2 + (3 * L - P₀) * P - 2 * P₀ * L = 0) := by sorry
end WhitinPrice.StyleGoods
