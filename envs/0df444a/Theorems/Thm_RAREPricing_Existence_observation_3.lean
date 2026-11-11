-- Prove2me | Theorems.Thm_RAREPricing_Existence_observation_3
-- name    : RAREPricing.Existence.observation_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:25:49.907203+00:00
-- url     : https://prove2.me/theorems/754bbc99-1de7-4073-b283-e8fe1ee7fbbf
-- title:
--   Observation 3 — total revenue is monotone in the sum of prices
-- statement:
--   Let $I$ be a market, fix the setting (rivalrous or non-rivalrous), and let $p,q\in\mathbb R^m_{\ge0}$ with $\sum_jp_j\le\sum_jq_j$. Then for every $x\in\mathrm{Dem}(p)$ and every $y\in\mathrm{Dem}(q)$,
--   $$R_{\mathrm{all}}(p,x)\le R_{\mathrm{all}}(q,y).$$
--
--   In the paper $R_{\mathrm{all}}(p)$ denotes the common value of $R_{\mathrm{all}}(p,x)$ over $x\in\mathrm{Dem}(p)$ (Observation 2), so this is the statement $R_{\mathrm{all}}(p)\le R_{\mathrm{all}}(q)$; in particular it holds for $x=A(p)$, $y=A(q)$ under any allocation rule.
--
--   Differences from the source:
--   - encoding: $R_{\mathrm{all}}(p)\le R_{\mathrm{all}}(q)$, with $R_{\mathrm{all}}(p)$ the value common to all demanded allocations → stated for every $x\in\mathrm{Dem}(p)$, $y\in\mathrm{Dem}(q)$, and for an arbitrary setting; reason: this is the paper's notation unfolded (the value does not depend on the demanded allocation), and "for both settings" is the quantifier over the setting.
-- source:
--   Chaudhury, Garg, Huang, Sharma, RARE: Response-Aware Rational Equilibrium in Budget-Constrained Pricing Games, STOC 2027 submission (manuscript sha256 e9bb863f…), p. 15 (PDF 17), Observation 3

import Mathlib
import Definitions.Def_RAREPricing_Existence_Model

namespace RAREPricing.Existence

theorem observation_3 {n m : ℕ} (M : Market n m) (s : Setting) (p q : Fin m → ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hsum : ∑ j, p j ≤ ∑ j, q j) :
    ∀ x ∈ Dem M s p, ∀ y ∈ Dem M s q, totalRevenue p x ≤ totalRevenue q y := by sorry

end RAREPricing.Existence
