-- Prove2me | Theorems.Thm_SystemicHoldings_FEfficient_lemma_4_1
-- name    : SystemicHoldings.FEfficient.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:28.357989+00:00
-- url     : https://prove2.me/theorems/7a16f8e1-66d0-4e9e-b5aa-23b6e0a86e77
-- title:
--   Lemma 4.1, p. 13 — the unique solution of (4.3) is y* = (bᵀv/1ᵀz)·z, z = G⁻¹1_K
-- statement:
--   Let $K\ge1$, $\mu\in\mathbb R^K$, $\sigma\in\mathbb R^K$ with all $\sigma_k>0$, and $b,v\in\mathbb R^N$. Let $G=\mu\mu^\top+\mathrm{Diag}(\sigma^2)$ and $\mathscr D_y=\{y\in\mathbb R^K\mid \mathbf 1_K^\top y=b^\top v\}$. The aggregate problem
--   $$\min_{y\in\mathscr D_y}\; y^\top G y \qquad (4.3)$$
--   has the unique solution
--   $$y^* = \frac{b^\top v}{\mathbf 1_K^\top z}\,z,\qquad z:=G^{-1}\mathbf 1_K .$$
--   That is, $y^*$ solves (4.3), and every solution of (4.3) equals $y^*$.
--
--   This is Step 1 ("aggregation") of the paper's two-step procedure: the aggregate $v$-weighted holdings of an f-efficient allocation are determined by $G$ and the scalar $b^\top v$ alone.
--
--   **Formalization Note** $K\ge1$ is added (for $K=0$ the formula divides by $0$); it is implicit in the paper's model. Assumption 3 is not needed and not assumed.
-- source:
--   Awiszus, Capponi & Weber, Market Efficient Portfolios in a Systemic Economy, arXiv:2003.10121v3, p. 13, Lemma 4.1

import Mathlib
import Definitions.Def_SystemicHoldings_FEfficient_Model

namespace SystemicHoldings.FEfficient
open Matrix

theorem lemma_4_1 {K N : ℕ} (hK : 1 ≤ K) (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (b v : Fin N → ℝ) :
    SolvesAggregate μ σ b v (yStar μ σ b v) ∧
    ∀ y : Fin K → ℝ, SolvesAggregate μ σ b v y → y = yStar μ σ b v := by sorry

end SystemicHoldings.FEfficient
