-- Prove2me | Theorems.Thm_RevenueOrdered_Ratio_revenue_le_weighted_sum
-- name    : RevenueOrdered.Ratio.revenue_le_weighted_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:48:23.043075+00:00
-- url     : https://prove2.me/theorems/1544f86c-dca6-481e-88e1-f3a3c11ceb18
-- title:
--   Proof of Theorem 3.2 — rev(S*) ≤ ∑_ℓ (r_ℓ − r_{ℓ−1})/r_ℓ · rev(S_ℓ)
-- statement:
--   Let $\mathcal P$ be a regular discrete choice model on a finite set of products $\mathcal C$, $r:\mathcal C\to\mathbb R_{>0}$, $r_1<\cdots<r_k$ the distinct values of $r$, $r_0:=0$, and $S_\ell=\{x : r(x)\ge r_\ell\}$. Then for every set $S^*\subseteq\mathcal C$,
--   $$
--   \sum_{x\in S^*}\mathcal P(x,S^*)\,r(x)\;\le\;\sum_{\ell=1}^{k}\frac{r_\ell-r_{\ell-1}}{r_\ell}\sum_{x\in S_\ell}\mathcal P(x,S_\ell)\,r(x).
--   $$
--
--   The revenue of any assortment is thus bounded by a nonnegative combination of the revenues of the revenue-ordered assortments, with weights $(r_\ell-r_{\ell-1})/r_\ell$. Bounding each $\operatorname{rev}(S_\ell)$ by the best one gives the sum form of Theorem 3.2.
--
--   **Formalization Note** The paper writes the inequality for an optimal $S^*$, with $\mathrm{OPT}$ on the left; it holds for every $S^*$ and is stated so.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 8, §3, proof of Theorem 3.2, rearranged display up to the first inequality

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered

namespace RevenueOrdered.Ratio

/-- Proof of Theorem 3.2 (p. 8), the rearranged display ending in the first inequality:
for an arbitrary set `Sstar`,
`∑_{x ∈ S*} 𝒫(x, S*) r(x) ≤ ∑_{ℓ=1}^{k} (r_ℓ − r_{ℓ−1})/r_ℓ · ∑_{x ∈ S_ℓ} 𝒫(x, S_ℓ) r(x)`. -/
theorem revenue_le_weighted_sum {C : Type*} [Fintype C] [DecidableEq C]
    (P : C → Finset C → ℝ) (hP : IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x)
    (Sstar : Finset C) :
    revenue P r Sstar ≤
      ∑ l ∈ Finset.Icc 1 (numVals r),
        (level r l - level r (l - 1)) / level r l * revenue P r (roSet r l) := by sorry

end RevenueOrdered.Ratio
