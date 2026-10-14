-- Prove2me | Theorems.Thm_RetailPrivacy_SingleFirm_lemma_1
-- name    : RetailPrivacy.SingleFirm.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:13:35.391378+00:00
-- url     : https://prove2.me/theorems/fea6dbea-2058-4054-bf3e-90fc42372ae7
-- title:
--   Lemma 1, p. 13 — hide-and-buy on [0, r(p)), disclose-and-buy on [r(p), 𝒯₁(p)], no purchase on (𝒯₁(p), 1]
-- statement:
--   Let $c>0$, $\delta\in(0,1)$, $v>0$ and a price $p \le v$, and let $(s,r)$ be a rational expectations equilibrium of the $\mathbb R$ mode with data collection at $p$ (so $r = r(p)$). Put
--   $$\mathcal T_1(p) = \min\left\{\frac{v-p-r\delta}{1-\delta},\ 1\right\}.$$
--   Then, among consumers $\theta\in[0,1]$:
--
--   1. those who buy and strictly prefer hiding to disclosing are exactly $\theta \in [0, r)$;
--   2. those who weakly prefer disclosing and get a nonnegative utility from buying and disclosing are exactly $\theta \in [r, \mathcal T_1(p)]$;
--   3. those whose best buying utility is negative (they do not buy) are exactly $\theta \in (\mathcal T_1(p), 1]$.
--
--   This is the three-segment structure (privacy-sensitive, privacy-insensitive, inactive consumers) used throughout the paper.
--
--   **Formalization Note** The lemma is stated for $p \le v$; for $p > v$ nobody buys and the printed intervals are meaningless. $r(p)$ and $\mathcal T_1(p)$ are read as the equilibrium intensity at $p$ and $\mathcal T_1(s,p)$ at that equilibrium. Consumers are classified by utility comparison, not by the paper's Table 1, whose purchase condition for disclosers is misprinted.
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), p. 13, Lemma 1; proof p. ec21

import Mathlib
import Definitions.Def_RetailPrivacy_SingleFirm_Model

namespace RetailPrivacy.SingleFirm

theorem lemma_1 (c δ v p s r : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v)
    (hp : p ≤ v) (hREE : IsREE .R true v c δ p s r) :
    {θ : ℝ | θ ∈ Set.Icc 0 1 ∧ utilDisclose v δ p r θ < utilHide v p θ ∧
        0 ≤ utilHide v p θ} = Set.Ico 0 r ∧
    {θ : ℝ | θ ∈ Set.Icc 0 1 ∧ utilHide v p θ ≤ utilDisclose v δ p r θ ∧
        0 ≤ utilDisclose v δ p r θ} = Set.Icc r (min ((v - p - r * δ) / (1 - δ)) 1) ∧
    {θ : ℝ | θ ∈ Set.Icc 0 1 ∧ buyUtil true v δ p r θ < 0} =
        Set.Ioc (min ((v - p - r * δ) / (1 - δ)) 1) 1 := by sorry

end RetailPrivacy.SingleFirm
