-- Prove2me | Theorems.Thm_SystemicHoldings_FEfficient_theorem_4_1
-- name    : SystemicHoldings.FEfficient.theorem_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:30.405429+00:00
-- url     : https://prove2.me/theorems/c28c3357-0a83-4695-9567-9ddd160b7b08
-- title:
--   Theorem 4.1, p. 14 — an f-efficient holding matrix exists with MSD (bᵀv)²/(1ᵀG⁻¹1); it is unique iff N = 2, and then equals Q^{N=2}
-- statement:
--   Consider $K$ assets and $N$ banks with $N,K\ge2$. Let $\mu\in\mathbb R^K$ be the mean price shocks and $\sigma\in\mathbb R^K$ their standard deviations, with $\sigma_k>0$ for all $k$ (Assumption 2), and $G=\mu\mu^\top+\mathrm{Diag}(\sigma^2)$. Let $q\in\mathbb R^K$ be the total holdings and $b\in\mathbb R^N$ the bank budgets, with $\sum_k q_k=\sum_i b_i$, and let $v\in\mathbb R^N$ be the systemic significance vector, satisfying Assumption 3: $v_i\neq v_j$ for some $i,j$, and $b^\top v\neq0$. A holding matrix $Q^*\in\mathscr D(q,b)=\{Q\mid Q\mathbf 1_N=q,\ \mathbf 1_K^\top Q=b^\top\}$ is f-efficient if it minimizes $\mathrm{MSD}(Q)=(Qv)^\top G(Qv)$ over $\mathscr D(q,b)$. Then:
--
--   1. **(a)** There exists an f-efficient holding matrix $Q^*$ with
--   $$\mathrm{MSD}(Q^*) = \frac{(b^\top v)^2}{\mathbf 1_K^\top G^{-1}\mathbf 1_K}.$$
--   2. **(b)** The f-efficient holding matrix is unique if and only if $N=2$.
--   3. In that case the f-efficient holding matrix is
--   $$Q^{N=2} := \frac{1}{v_2-v_1}\big(\,v_2q-y^* \;\;\; y^*-v_1q\,\big)\in\mathbb R^{K\times2},\qquad y^*=\frac{b^\top v}{\mathbf 1_K^\top G^{-1}\mathbf 1_K}G^{-1}\mathbf 1_K .$$
--
--   The theorem gives the minimal achievable mean squared deviation of market capitalization from its fundamental value, and shows that with three or more banks the regulator's optimal allocation is not pinned down by efficiency alone.
--
--   **Formalization Note** The hypothesis $\sum_k q_k=\sum_i b_i$ is added: the paper derives it on p. 11 ("We then obtain $\sum q_k=\sum b_i=:T$"), and without it $\mathscr D(q,b)$ is empty and (a) is false. The vector $v$ is a free parameter subject to Assumption 3 (the paper defines it from the primitives by (3.1); all of Section 4 holds for any such $v$). The paper's banks 1 and 2 are the indices `0` and `1`, and $Q^{N=2}$ is stated through a `Fin.cast` along $N=2$. Part (b) is `∃!` iff $N=2$; together with it, the last clause identifies the unique matrix. f-efficiency is the argmin of Definition 1.
-- source:
--   Awiszus, Capponi & Weber, Market Efficient Portfolios in a Systemic Economy, arXiv:2003.10121v3, p. 14, Theorem 4.1

import Mathlib
import Definitions.Def_SystemicHoldings_FEfficient_Model

namespace SystemicHoldings.FEfficient
open Matrix

theorem theorem_4_1 {K N : ℕ} (hK : 2 ≤ K) (hN : 2 ≤ N)
    (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (q : Fin K → ℝ) (b v : Fin N → ℝ)
    (hT : ∑ k, q k = ∑ i, b i)
    (hA3 : Assumption3 b v) :
    (∃ Q : Matrix (Fin K) (Fin N) ℝ, IsFEfficient μ σ q b v Q ∧
        msd μ σ v Q = (b ⬝ᵥ v) ^ 2 /
          ((fun _ => (1 : ℝ)) ⬝ᵥ ((shockMoment μ σ)⁻¹ *ᵥ (fun _ => (1 : ℝ))))) ∧
    ((∃! Q : Matrix (Fin K) (Fin N) ℝ, IsFEfficient μ σ q b v Q) ↔ N = 2) ∧
    (∀ h : N = 2, IsFEfficient μ σ q b v
        (fun k i => QN2 q (yStar μ σ b v) (fun j => v (Fin.cast h.symm j)) k (Fin.cast h i))) := by sorry

end SystemicHoldings.FEfficient
