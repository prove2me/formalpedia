-- Prove2me | Theorems.Thm_TargetGranularity_SdVsMd_sd_profit_bounded_below_small_cad
-- name    : TargetGranularity.SdVsMd.sd_profit_bounded_below_small_cad
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-31T19:55:06.412704+00:00
-- url     : https://prove2.me/theorems/e5bff063-079b-438c-823d-0515cfb85311
-- title:
--   Proof of Proposition 3, pp. 40–41 — at a fixed c_click ∈ ((1−p)²/2, (1−p)/2), the sd equilibrium profit is bounded away from 0 for all small c_ad
-- statement:
--   Fix a price $p\in(0,1)$ and a click cost $c^*$ with
--   $$\frac{(1-p)^2}{2} < c^* < \frac{1-p}{2}.$$
--   Then the sd-targeting equilibrium profit at $c_{click}=c^*$ stays bounded away from $0$ as the unit ad cost vanishes: there are $\varepsilon>0$ and $\delta>0$ such that for every $c_{ad}\in(0,\delta)$, every non-trivial sd equilibrium $\Sigma^{sd}$ (a measurable $\Sigma\subseteq[0,1]$ of positive length that is a best response to the click set its own posterior induces) satisfies
--   $$\Pi^{*sd}(c_{ad}, c^*, p) \ge \varepsilon.$$
--
--   This is the uniformity step implicit in the closing paragraph of the proof of Proposition 3 (p. 41): the paper combines Lemma 4 (sd profit is decreasing in $c_{click}$ on $((1-p)^2/2,(1-p)/2]$ and vanishes only at $(1-p)/2$), Lemma 5 ($\Pi^{*md}\to 0$ at $c^{max}_{click}$ as $c_{ad}\to0$) and the limit $c^{max}_{click}\to\frac{1-p}{2(1+p)}<\frac{1-p}{2}$ (proof of Corollary 2, p. 42) to conclude that, for small $c_{ad}$, sd profit near $c^{max}_{click}$ exceeds md profit. That conclusion needs the sd profit at a click cost strictly below $(1-p)/2$ to remain positive uniformly as $c_{ad}\to 0$, which is what this lemma states. Intuition: with $c_{click}=c^*<(1-p)/2$ the equilibrium click set $[\bar\omega^*,1]$ cannot collapse (if it did, the firm would target only $\alpha\gtrsim p$ and the type $\omega=1$ would enjoy surplus close to $(1-p)/2>c^*$), so the equilibrium profit, which tends to $\int p\,G(\alpha;\bar\omega)\,d\alpha>0$, stays bounded below.
-- source:
--   Despotakis & Yu, Multidimensional Targeting and Consumer Response, SSRN 3900394 (version of October 11, 2022), proof of Proposition 3, pp. 40–41 (PDF 41–42): the step 'there exist δ, δ′(δ) > 0 such that for c_ad < δ, c_click = c^max_click(c_ad,p) − δ′ ... the profit under sd-targeting is larger', combining Lemma 4 (p. 40) with the limit c^max_click → (1−p)/(2(1+p)) from the proof of Corollary 2 (p. 42)

import Mathlib
import Definitions.Def_TargetGranularity_SdVsMd_Model

namespace TargetGranularity.SdVsMd

/-- Step of the proof of Proposition 3, pp. 40–41 (with Lemma 4 and the limit computation in the
proof of Corollary 2, p. 42): for a fixed click cost `c* ∈ ((1−p)²/2, (1−p)/2)`, the sd
equilibrium profit stays bounded away from `0` as `c_ad → 0`: there are `ε > 0` and `δ > 0` such
that every non-trivial sd equilibrium with `c_ad ∈ (0, δ)` and `c_click = c*` earns at least `ε`. -/
theorem sd_profit_bounded_below_small_cad (p cstar : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hlo : (1 - p) ^ 2 / 2 < cstar) (hhi : cstar < (1 - p) / 2) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∀ cad : ℝ, 0 < cad → cad < δ →
      ∀ S : Set ℝ, IsSdEq p cad cstar S → ε ≤ sdProfit p cad cstar S := by sorry

end TargetGranularity.SdVsMd
