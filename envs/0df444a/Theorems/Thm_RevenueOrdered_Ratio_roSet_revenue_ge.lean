-- Prove2me | Theorems.Thm_RevenueOrdered_Ratio_roSet_revenue_ge
-- name    : RevenueOrdered.Ratio.roSet_revenue_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:47:58.154974+00:00
-- url     : https://prove2.me/theorems/97ddb3a2-f51f-471c-93c2-a8ed1a0dfaf7
-- title:
--   Inequality (5) — rev(S_i) ≥ r_i · ∑_{x∈S*∩S_i} 𝒫(x, S*)
-- statement:
--   Let $\mathcal P$ be a regular discrete choice model on a finite set of products $\mathcal C$, let $r:\mathcal C\to\mathbb R_{>0}$, let $r_1<\cdots<r_k$ be the distinct values of $r$ and $S_i=\{x : r(x)\ge r_i\}$ the revenue-ordered assortments. Then for every set $S^*\subseteq\mathcal C$ and every $i\in[k]$,
--   $$
--   \sum_{x\in S_i}\mathcal P(x,S_i)\,r(x)\;\ge\;\sum_{x\in S^*\cap S_i}\mathcal P(x,S^*)\,r_i .
--   $$
--
--   This is the technical observation (5) of the paper, which drives the proofs of Theorems 3.1 and 3.2: the revenue of $S_i$ is at least $r_i$ times the probability that an arbitrary assortment $S^*$ sells a product of revenue at least $r_i$.
--
--   **Formalization Note** The paper introduces (5) for an optimal solution $S^*$, but its proof does not use optimality, so it is stated here for every $S^*$.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 7, §3, proof of Theorem 3.1, inequality (5)

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered

namespace RevenueOrdered.Ratio

/-- Inequality (5) (p. 7, proof of Theorem 3.1), stated for an arbitrary set `Sstar`:
`∑_{x ∈ S_i} 𝒫(x, S_i) r(x) ≥ ∑_{x ∈ S* ∩ S_i} 𝒫(x, S*) r_i` for every `i ∈ [k]`. -/
theorem roSet_revenue_ge {C : Type*} [Fintype C] [DecidableEq C]
    (P : C → Finset C → ℝ) (hP : IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x)
    (Sstar : Finset C) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ numVals r) :
    ∑ x ∈ Sstar ∩ roSet r i, P x Sstar * level r i ≤ revenue P r (roSet r i) := by sorry

end RevenueOrdered.Ratio
