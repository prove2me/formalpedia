-- Prove2me | Theorems.Thm_SystemicHoldings_FEfficient_proposition_4_1
-- name    : SystemicHoldings.FEfficient.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:25.145933+00:00
-- url     : https://prove2.me/theorems/38bf1d55-97fa-4ab3-bae4-b6570d414c88
-- title:
--   Proposition 4.1, p. 13 — Q* ∈ 𝒟 is f-efficient iff Q*v solves the aggregate problem (4.3)
-- statement:
--   Let $N\ge2$, $K\ge1$, $\mu,\sigma\in\mathbb R^K$ with all $\sigma_k>0$, $q\in\mathbb R^K$, $b,v\in\mathbb R^N$ with $v_i\neq v_j$ for some $i,j$, and let $Q^*\in\mathscr D(q,b)$. The following are equivalent:
--
--   1. $Q^*$ is f-efficient, i.e. $Q^*$ minimizes $\mathrm{MSD}(Q)=(Qv)^\top G(Qv)$ over $\mathscr D(q,b)$;
--   2. $y^* := Q^*v$ solves the aggregate problem
--   $$\min_{y\in\mathscr D_y} y^\top G y,\qquad \mathscr D_y=\{y\in\mathbb R^K\mid\mathbf 1_K^\top y=b^\top v\}.$$
--
--   This justifies the paper's "aggregate first, then allocate" procedure: a $KN$-dimensional quadratic program reduces to a $K$-dimensional one.
--
--   **Formalization Note** The matrix $Q^*$ is fixed and assumed feasible, matching "(ii) $y^*=Q^*v$ for some $Q^*\in\mathscr D$". Only the first half of Assumption 3 is assumed; without it the statement is false (if all $v_i$ coincide, every feasible matrix is f-efficient, but $Q^*v=v_1q$ need not solve (4.3)). No hypothesis $\sum_k q_k=\sum_i b_i$ is needed, since it follows from $Q^*\in\mathscr D(q,b)$.
-- source:
--   Awiszus, Capponi & Weber, Market Efficient Portfolios in a Systemic Economy, arXiv:2003.10121v3, p. 13, Proposition 4.1

import Mathlib
import Definitions.Def_SystemicHoldings_FEfficient_Model

namespace SystemicHoldings.FEfficient
open Matrix

theorem proposition_4_1 {K N : ℕ} (hN : 2 ≤ N) (hK : 1 ≤ K)
    (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (q : Fin K → ℝ) (b v : Fin N → ℝ) (hv : ∃ i j, v i ≠ v j)
    (Q : Matrix (Fin K) (Fin N) ℝ) (hQ : Q ∈ feasible q b) :
    IsFEfficient μ σ q b v Q ↔ SolvesAggregate μ σ b v (Q *ᵥ v) := by sorry

end SystemicHoldings.FEfficient
