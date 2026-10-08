-- Prove2me | Theorems.Thm_RetailVariety_Statics_theorem_2
-- name    : RetailVariety.Statics.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:15.449843+00:00
-- url     : https://prove2.me/theorems/cbc34a07-02ab-4517-9535-99dbf1e5650c
-- title:
--   Theorem 2: optimal variety rises with price $p$ and volume $\lambda$, falls as $v_0\to0$
-- statement:
--   Let $n>i\ge1$, let the variant preferences be ordered $v_1\ge v_2\ge\dots\ge v_n>0$, and let $A_i=\{1,\dots,i\}$ be the set of the $i$ most popular variants. Fix the unit cost $c>0$ and the demand parameters $\sigma>0$, $0\le\beta<1$. Let $\pi_I$ and $\pi_T$ be the optimal expected profits (7) and (8) of the independent and trend-following population models, with $z=\Phi^{-1}(1-c/p)$ moving with the price $p$.
--
--   1. **(a) Price.** For every store volume $\lambda>0$ and no-purchase preference $v_0>0$, for all sufficiently high selling prices $p$,
--   $$\pi_I(A_{i+1},v)>\pi_I(A_i,v)\quad\text{and}\quad\pi_T(A_{i+1},v)>\pi_T(A_i,v).$$
--   2. **(b) No-purchase preference.** For every price $p>c$ and volume $\lambda>0$, for all sufficiently small $v_0>0$,
--   $$\pi_I(A_{i+1},v)<\pi_I(A_i,v);$$
--   and, if in addition $p\,v_1>c\sum_{j=1}^{i}v_j$, for all sufficiently small $v_0>0$,
--   $$\pi_T(A_{i+1},v)<\pi_T(A_i,v).$$
--   3. **(c) Store volume (independent model only).** For every price $p>c$ and $v_0>0$, for all sufficiently large $\lambda$,
--   $$\pi_I(A_{i+1},v)>\pi_I(A_i,v).$$
--
--   Since the optimal assortment is a prefix set $A_k$ (Theorem 1 of the paper), these comparisons say that higher margins and higher store traffic favour broader assortments, while a weaker outside option favours narrower ones; the trend-following model shows no volume effect because its profit is proportional to $\lambda$.
--
--   **Formalization Note** "Sufficiently high/low" is an eventual statement: `∀ᶠ p in atTop`, `∀ᶠ v0 in 𝓝[>] 0`, `∀ᶠ lam in atTop`; parameters not being varied are fixed and universally quantified. In the trend-following case of (b) the paper's statement is false without an extra condition: e.g. $n=3$, $v=(1,1,1)$, $i=2$, $p=1.5c$ gives $\pi_T(A_2,v)=\pi_T(A_3,v)=0$ for every $v_0>0$. The hypothesis $p v_1>c\sum_{j\le i}v_j$ (variant 1 earns a positive margin on $A_i$ in the limit $v_0\to0$) is added there and only there; it is also necessary for the strict inequality. Variants are 0-indexed in Lean, so $v_1$ is `v ⟨0, _⟩`.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1504, Theorem 2

import Mathlib
import Definitions.Def_RetailVariety_Statics_Model

open Filter Topology

namespace RetailVariety.Statics

theorem theorem_2 (n i : ℕ) (hi : 1 ≤ i) (hin : i < n) (v : Fin n → ℝ) (hv : ∀ j, 0 < v j)
    (hanti : Antitone v) (c σ β : ℝ) (hc : 0 < c) (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    -- (a) sufficiently high selling price p, both demand models
    (∀ lam v0 : ℝ, 0 < lam → 0 < v0 →
      (∀ᶠ p in atTop,
          RetailVariety.Structure.profitI p c lam σ β v v0 (A n i) < RetailVariety.Structure.profitI p c lam σ β v v0 (A n (i + 1))) ∧
      (∀ᶠ p in atTop,
          RetailVariety.Structure.profitT p c lam v v0 (A n i) < RetailVariety.Structure.profitT p c lam v v0 (A n (i + 1)))) ∧
    -- (b) sufficiently low no-purchase preference v0, both demand models
    (∀ p lam : ℝ, c < p → 0 < lam →
      (∀ᶠ v0 in 𝓝[>] 0,
          RetailVariety.Structure.profitI p c lam σ β v v0 (A n (i + 1)) < RetailVariety.Structure.profitI p c lam σ β v v0 (A n i)) ∧
      (c * ∑ j ∈ A n i, v j < p * v ⟨0, by omega⟩ →
        ∀ᶠ v0 in 𝓝[>] 0,
          RetailVariety.Structure.profitT p c lam v v0 (A n (i + 1)) < RetailVariety.Structure.profitT p c lam v v0 (A n i))) ∧
    -- (c) sufficiently high store volume lam, independent population model only
    (∀ p v0 : ℝ, c < p → 0 < v0 →
      ∀ᶠ lam in atTop,
          RetailVariety.Structure.profitI p c lam σ β v v0 (A n i) < RetailVariety.Structure.profitI p c lam σ β v v0 (A n (i + 1))) := by sorry

end RetailVariety.Statics
