-- Prove2me | Theorems.Thm_RevenueOrdered_Ratio_revenue_eq_layer_sum
-- name    : RevenueOrdered.Ratio.revenue_eq_layer_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:48:13.508297+00:00
-- url     : https://prove2.me/theorems/7fb8f3b3-e506-4af9-a600-c2c84e2b19a0
-- title:
--   Proof of Theorem 3.2 — rev(S*) = ∑_ℓ (r_ℓ − r_{ℓ−1}) ∑_{x∈S*∩S_ℓ} 𝒫(x, S*)
-- statement:
--   Let $\mathcal C$ be a finite set of products, $\mathcal P$ any system of choice probabilities, $r:\mathcal C\to\mathbb R_{>0}$, $r_1<\cdots<r_k$ the distinct values of $r$, $r_0:=0$, and $S_\ell=\{x : r(x)\ge r_\ell\}$. Then for every set $S^*\subseteq\mathcal C$,
--   $$
--   \sum_{x\in S^*}\mathcal P(x,S^*)\,r(x)\;=\;\sum_{\ell=1}^{k}(r_\ell-r_{\ell-1})\sum_{x\in S^*\cap S_\ell}\mathcal P(x,S^*).
--   $$
--
--   This is the rearrangement (summation by parts over the distinct revenues) with which the proof of Theorem 3.2 begins: each revenue $r(x)=r_i$ is written as the telescoping sum $\sum_{\ell\le i}(r_\ell-r_{\ell-1})$.
--
--   **Formalization Note** The paper writes the identity for an optimal $S^*$, with $\mathrm{OPT}$ on the left; it holds for every $S^*$ and is stated so. No regularity axiom is needed.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 8, §3, proof of Theorem 3.2, first two equalities of the rearranged display

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered

namespace RevenueOrdered.Ratio

/-- Proof of Theorem 3.2 (p. 8), the first two equalities of the rearranged display:
`∑_{x ∈ S*} 𝒫(x, S*) r(x) = ∑_{ℓ=1}^{k} (r_ℓ − r_{ℓ−1}) ∑_{x ∈ S* ∩ S_ℓ} 𝒫(x, S*)`,
with `r_0 = 0`, for an arbitrary set `Sstar`. -/
theorem revenue_eq_layer_sum {C : Type*} [Fintype C] [DecidableEq C]
    (P : C → Finset C → ℝ) (r : C → ℝ) (hr : ∀ x, 0 < r x) (Sstar : Finset C) :
    revenue P r Sstar =
      ∑ l ∈ Finset.Icc 1 (numVals r),
        (level r l - level r (l - 1)) * ∑ x ∈ Sstar ∩ roSet r l, P x Sstar := by sorry

end RevenueOrdered.Ratio
