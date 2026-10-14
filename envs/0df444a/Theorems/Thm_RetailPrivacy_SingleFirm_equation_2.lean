-- Prove2me | Theorems.Thm_RetailPrivacy_SingleFirm_equation_2
-- name    : RetailPrivacy.SingleFirm.equation_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:13:40.537526+00:00
-- url     : https://prove2.me/theorems/7ca0175a-8619-49f0-a785-632d8610eeca
-- title:
--   (2), p. 13 — the rational-expectations solution r(p), s(p) and 𝒯₁(p) = min{(v−p)𝒵/(2c(1−δ)+δ), 1}, with the saturated branch
-- statement:
--   Let $c>0$, $\delta\in(0,1)$, $v>0$, and a price $p \le v$. Write $D = 2c(1-\delta)+\delta$ and $\mathcal Z = 2c+\delta$. Under the $\mathbb R$ mode with data collection, a pair $(s,r)$ is a rational expectations equilibrium of the consumer and exploitation stages if and only if
--
--   1. $(v-p)\mathcal Z \le D$ and $s = \dfrac{2c(v-p)}{D}$, $r = \dfrac{\delta(v-p)}{D}$; or
--   2. $(v-p)\mathcal Z > D$ and $s = \dfrac{2c}{\mathcal Z}$, $r = \dfrac{\delta}{\mathcal Z}$.
--
--   In either case the sales quantity is
--   $$\mathcal T_1(p) = \min\left\{\frac{(v-p)\mathcal Z}{2c(1-\delta)+\delta},\ 1\right\}.$$
--
--   In particular the equilibrium of the consumer stage exists and is unique at every price $p \le v$; this is what reduces the firm's pricing problem to a function of $p$ alone.
--
--   **Formalization Note** The paper prints $r(p) = \delta(v-p)/(2c(1-\delta)+\delta)$ for every $p$. That formula solves the rational-expectations equation only on the unsaturated range $(v-p)\mathcal Z \le D$; when the market is saturated the solution is $r = \delta/\mathcal Z$. The statement gives both branches. The price is restricted to $p \le v$ (for $p > v$ nobody buys and $s = r = 0$).
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), p. 13, (2); proof of Proposition 1, p. ec21

import Mathlib
import Definitions.Def_RetailPrivacy_SingleFirm_Model

namespace RetailPrivacy.SingleFirm

theorem equation_2 (c δ v p s r : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v)
    (hp : p ≤ v) :
    (IsREE .R true v c δ p s r ↔
      ((v - p) * Zc c δ ≤ 2 * c * (1 - δ) + δ ∧
          s = 2 * c * (v - p) / (2 * c * (1 - δ) + δ) ∧
          r = δ * (v - p) / (2 * c * (1 - δ) + δ)) ∨
        (2 * c * (1 - δ) + δ < (v - p) * Zc c δ ∧
          s = 2 * c / Zc c δ ∧ r = δ / Zc c δ)) ∧
    (IsREE .R true v c δ p s r →
      demand true v δ p r = min ((v - p) * Zc c δ / (2 * c * (1 - δ) + δ)) 1) := by sorry

end RetailPrivacy.SingleFirm
