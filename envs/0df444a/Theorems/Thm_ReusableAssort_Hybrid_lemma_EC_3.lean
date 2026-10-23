-- Prove2me | Theorems.Thm_ReusableAssort_Hybrid_lemma_EC_3
-- name    : ReusableAssort.Hybrid.lemma_EC_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:39.27311+00:00
-- url     : https://prove2.me/theorems/831e0123-e30b-4ba7-b093-dffd1751a02d
-- title:
--   Lemma EC.3, ec13 — the per-unit revenue-to-go of Algorithm 3 is at least the optimistic DP value
-- statement:
--   Fix an instance satisfying the model assumptions, a feasible normalized LP solution $y$, a time $t \in [T]$ and a product $i$. Start the online process at time $t$ in an inventory state $\mathbf J$: some units of each product are out and due back at given times in $(t, t+T]$, at most $c_j$ of product $j$, and $J_t$ units of product $i$ are on hand. Product $i$ uses the revenue thresholds $P^{z}_{i,s}$ of Algorithm 3 and every other product an arbitrary valid rule. Let $\mathcal Q_{i,t}(\mathbf J)$ be the per-unit revenue of product $i$ generated in $[t : T]$, i.e. its total expected revenue divided by $J_t$. Then
--   $$\mathcal Q_{i,t}(\mathbf J) \ge \mathcal V_{i,t},$$
--   where $\mathcal V$ is the optimistic per-unit DP (3).
--
--   Applied at $t = 1$ with full inventory it shows that Algorithm 3 earns at least $c_i \mathcal V_{i,1}$ from product $i$ (Part (i) of the proof of Theorem 2).
--
--   **Formalization Note** The inequality is stated multiplied out, $J_t\, \mathcal V_{i,t} \le \mathbb E[\text{revenue of } i \text{ in } [t:T]]$, which avoids the division by $J_t = 0$ (it is equivalent for $J_t > 0$). The page's states satisfy $\sum_{\tau \ge t} J_\tau = c_i$ with all returns within the horizon; here units may be due after $T$ as well, and the units of product $i$ on hand are $c_i$ minus those still out. The rules of the other products are arbitrary, and $y$ need only be feasible.
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. ec13 (PDF 39), Lemma EC.3 (state J and Q_{i,t}(J) defined on ec12)

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Algorithms

namespace ReusableAssort.Hybrid

theorem lemma_EC_3 {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]
    (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPFeasible I y) (hN : Normalized I y)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 T)
    (ret : Fin n → ℕ → ℕ) (hret : ValidStart I t ret)
    (rule : Fin n → Rule Z) (hrule : ∀ j, (rule j).Valid)
    (i : Fin n) (hi : rule i = Rule.threshold (P I y i)) :
    ((I.c i - ∑ s ∈ Finset.Ioc t (t + T), ret i s : ℕ) : ℝ) * V I y i t
      ≤ expRevProd I y rule t ret i := by sorry

end ReusableAssort.Hybrid
