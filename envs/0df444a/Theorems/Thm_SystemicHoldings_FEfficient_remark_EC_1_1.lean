-- Prove2me | Theorems.Thm_SystemicHoldings_FEfficient_remark_EC_1_1
-- name    : SystemicHoldings.FEfficient.remark_EC_1_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:21.325003+00:00
-- url     : https://prove2.me/theorems/94be1c58-e9ae-4772-94de-698bec88674a
-- title:
--   Remark EC.1.1, EC pp. 8–9 — Q* is f-efficient iff F vec(Q*) = (b, q, y*)
-- statement:
--   Let $N\ge2$, $K\ge1$, $\mu,\sigma\in\mathbb R^K$ with all $\sigma_k>0$, $q\in\mathbb R^K$, and $b,v\in\mathbb R^N$ with $v_i\neq v_j$ for some $i,j$. For every $Q^*\in\mathbb R^{K\times N}$,
--   $$Q^*\text{ is f-efficient}\iff F\,\mathrm{vec}(Q^*) = \begin{pmatrix} b\\ q\\ y^*\end{pmatrix},\qquad (\text{EC.1.12})$$
--   where $F\in\mathbb R^{(2K+N)\times KN}$ stacks the budget rows $\mathbf 1_K^\top Q^* = b^\top$, the supply rows $Q^*\mathbf 1_N=q$ and the rows $Q^*v=y^*$, and $y^*$ is the solution of the aggregate problem from Lemma 4.1.
--
--   So the set of f-efficient holding matrices is the solution set of a linear system; its dimension is governed by the null space of $F$.
--
--   **Formalization Note** $\mathrm{vec}(Q^*)$ is indexed by pairs (asset $k$, bank $j$) rather than by stacked columns, and the right-hand side $(b,q,y^*)$ by `Fin N ⊕ Fin K ⊕ Fin K`. Only the first half of Assumption 3 is assumed, as in Proposition 4.1. $\sum_k q_k=\sum_i b_i$ is not assumed: if it fails, both sides are false.
-- source:
--   Awiszus, Capponi & Weber, Market Efficient Portfolios in a Systemic Economy, arXiv:2003.10121v3, E-Companion pp. 8–9 (PDF 38–39), Remark EC.1.1, (EC.1.12)

import Mathlib
import Definitions.Def_SystemicHoldings_FEfficient_Model

namespace SystemicHoldings.FEfficient
open Matrix

theorem remark_EC_1_1 {K N : ℕ} (hN : 2 ≤ N) (hK : 1 ≤ K)
    (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (q : Fin K → ℝ) (b v : Fin N → ℝ) (hv : ∃ i j, v i ≠ v j)
    (Q : Matrix (Fin K) (Fin N) ℝ) :
    IsFEfficient μ σ q b v Q ↔
      Fmat v *ᵥ (fun c : Fin K × Fin N => Q c.1 c.2) =
        Sum.elim b (Sum.elim q (yStar μ σ b v)) := by sorry

end SystemicHoldings.FEfficient
