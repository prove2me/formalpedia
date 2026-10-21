-- Prove2me | Theorems.Thm_SystemicHoldings_FEfficient_proposition_4_2
-- name    : SystemicHoldings.FEfficient.proposition_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:17.120206+00:00
-- url     : https://prove2.me/theorems/a762a435-48ef-40bc-8a64-540ba8044427
-- title:
--   Proposition 4.2, p. 14 — for N ≥ 2, K ≥ 1 there is Q* ∈ 𝒟 with Q*v = y*
-- statement:
--   Let $N\ge2$, $K\ge1$, $\mu\in\mathbb R^K$, $\sigma\in\mathbb R^K$ with all $\sigma_k>0$, $q\in\mathbb R^K$ and $b,v\in\mathbb R^N$ with $\sum_k q_k=\sum_i b_i$, and suppose $v_i\neq v_j$ for some $i,j$. Then there exists a matrix
--   $$Q^*\in\mathscr D(q,b)\quad\text{with}\quad Q^*v=y^*,$$
--   where $y^*=\frac{b^\top v}{\mathbf 1_K^\top G^{-1}\mathbf 1_K}G^{-1}\mathbf 1_K$ is the solution of the aggregate problem from Lemma 4.1.
--
--   This is Step 2 ("allocation") of the two-step procedure: the aggregate holdings are always realizable by a feasible allocation.
--
--   **Formalization Note** The hypothesis $\sum_k q_k=\sum_i b_i$ is added; the paper derives it on p. 11 from the nonemptiness of $\mathscr D(q,b)$, and without it $\mathscr D(q,b)=\emptyset$. Only the first half of Assumption 3 ($v$ not constant) is used, as in the paper's proof; the paper's "w.l.o.g. $v_2\neq v_1$" relabelling is left to the proof.
-- source:
--   Awiszus, Capponi & Weber, Market Efficient Portfolios in a Systemic Economy, arXiv:2003.10121v3, p. 14, Proposition 4.2

import Mathlib
import Definitions.Def_SystemicHoldings_FEfficient_Model

namespace SystemicHoldings.FEfficient
open Matrix

theorem proposition_4_2 {K N : ℕ} (hN : 2 ≤ N) (hK : 1 ≤ K)
    (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (q : Fin K → ℝ) (b v : Fin N → ℝ) (hT : ∑ k, q k = ∑ i, b i)
    (hv : ∃ i j, v i ≠ v j) :
    ∃ Q ∈ feasible q b, Q *ᵥ v = yStar μ σ b v := by sorry

end SystemicHoldings.FEfficient
