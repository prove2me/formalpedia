-- Prove2me | Theorems.Thm_SPPRevenue_SingleUnit_Supplement_lemma_7
-- name    : SPPRevenue.SingleUnit.Supplement.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:18:15.778908+00:00
-- url     : https://prove2.me/theorems/6f8cac5a-606f-4689-aca7-4b896fb11a37
-- title:
--   Lemma 7 — Σ_j(α_j − α_{j+1})x_i^j satisfies the click inequalities (8)
-- statement:
--   Let $1\ge\alpha_1\ge\dots\ge\alpha_n\ge0$ be click-through rates, $\alpha_{n+1}=0$. Suppose that $x^j_i\in[0,1]$ for all $i,j\in[n]$ and $\sum_{i\in[n]}x^j_i\le j$ for every $j\in[n]$. Then $x_i=\sum_{j\in[n]}(\alpha_j-\alpha_{j+1})x^j_i$ satisfies the feasibility conditions (8):
--   $$\sum_{i\in S}x_i\ \le\ \sum_{j=1}^{|S|}\alpha_j\qquad\text{for every }S\subseteq[n].$$
--
--   With Lemma 5 this shows that combining $j$-unit allocations with the weights $\alpha_j-\alpha_{j+1}$ gives a realizable vector of expected clicks; it is used for the SPP mechanism of Theorem 4.
--
--   **Formalization Note** $x$ is indexed as `x j i` $=x^{j+1}_{i+1}$ (0-based), so the capacity of index $j$ is $j+1$.
--
--   Differences from the source:
--   - encoding: i, j ∈ [n], α_{n+1} = 0 → indices of Fin n shifted by one; ctrGap α j = α_j − α_{j+1} with α_{n+1} = 0; reason: Lean indexing; same statement
--   - encoding: the click-through rates of §6.1, 1 ≥ α_1 ≥ … ≥ α_n ≥ 0 → hypothesis IsCTR α; reason: the standing assumption of the position-auction setting, stated as a binder
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, p. 24, Lemma 7 and its proof; (8) on p. 21

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Position

namespace SPPRevenue.SingleUnit.Supplement

theorem lemma_7 {n : ℕ} (α : Fin n → ℝ) (hα : IsCTR α) (x : Fin n → Fin n → ℝ)
    (hx : ∀ j i, 0 ≤ x j i ∧ x j i ≤ 1) (hcap : ∀ j : Fin n, ∑ i, x j i ≤ (j : ℝ) + 1) :
    ClickIneq α (fun i => ∑ j, ctrGap α j * x j i) := by sorry

end SPPRevenue.SingleUnit.Supplement
