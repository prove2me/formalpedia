-- Prove2me | Theorems.Thm_RetailPrivacy_SupplyChain_lemma_1
-- name    : RetailPrivacy.SupplyChain.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:42.53269+00:00
-- url     : https://prove2.me/theorems/708a47aa-1f0b-42a0-8fac-2e9e67379151
-- title:
--   Lemma 1, p. 13 (restated for §5, p. 19) — hide-buy on [0, r), disclose-buy on [r, 𝒯₁], no purchase on (𝒯₁, 1]
-- statement:
--   Consider the ℝ mode with data collection. Let $p \le v$ be a retail price and let $(s, r)$ be the rational expectations equilibrium of the consumer stage at $p$: $r$ maximizes $r'\delta s - c r'^2$ over $r' \ge 0$, and $s$ is the measure of consumers who buy and disclose given $r$. Write
--   $$\mathcal T_1 = \min\Big\{\frac{v - p - r\delta}{1-\delta},\ 1\Big\}.$$
--   Then, within $[0,1]$:
--
--   1. the consumers who buy and strictly prefer hiding their data are exactly those with $\theta \in [0, r)$;
--   2. the consumers who buy and (weakly) prefer disclosing are exactly those with $\theta \in [r, \mathcal T_1]$;
--   3. the consumers who do not buy are exactly those with $\theta \in (\mathcal T_1, 1]$.
--
--   This is the partition of the market into privacy-sensitive, privacy-insensitive and inactive consumers; the paper notes that it "continues to hold in Section 5" (p. 19), since the consumer stage of the supply chain is that of the single-firm model.
--
--   **Formalization Note** The statement is restricted to $p \le v$: for $p > v$ nobody buys and the printed intervals are meaningless. Here $r$ is the equilibrium intensity at $p$ (the paper's $r(p)$), and $\mathcal T_1$ is written in terms of $r$ rather than through the closed form (2). The standing assumptions $c > 0$, $\delta\in(0,1)$ and $v > 0$ are carried as hypotheses.
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), p. 13, Lemma 1; p. 19, §5.1 first paragraph

import Mathlib
import Definitions.Def_RetailPrivacy_SupplyChain_Model

namespace RetailPrivacy.SupplyChain

theorem lemma_1 (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v)
    (p s r : ℝ) (hp : p ≤ v) (hREE : RetailPrivacy.SingleFirm.IsREE .R true v c δ p s r) :
    {θ : ℝ | θ ∈ Set.Icc 0 1 ∧ 0 ≤ RetailPrivacy.SingleFirm.buyUtil true v δ p r θ ∧
        RetailPrivacy.SingleFirm.utilDisclose v δ p r θ < RetailPrivacy.SingleFirm.utilHide v p θ} = Set.Ico 0 r ∧
    {θ : ℝ | θ ∈ Set.Icc 0 1 ∧ 0 ≤ RetailPrivacy.SingleFirm.buyUtil true v δ p r θ ∧
        RetailPrivacy.SingleFirm.utilHide v p θ ≤ RetailPrivacy.SingleFirm.utilDisclose v δ p r θ} = Set.Icc r (min ((v - p - r * δ) / (1 - δ)) 1) ∧
    {θ : ℝ | θ ∈ Set.Icc 0 1 ∧ RetailPrivacy.SingleFirm.buyUtil true v δ p r θ < 0} = Set.Ioc (min ((v - p - r * δ) / (1 - δ)) 1) 1 := by sorry

end RetailPrivacy.SupplyChain
