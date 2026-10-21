-- Prove2me | Theorems.Thm_SqrtAgreement_SRA_payoff_decomposition
-- name    : SqrtAgreement.SRA.payoff_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:41.56813+00:00
-- url     : https://prove2.me/theorems/008dea25-e881-4ce6-89db-a5cf846c9af6
-- title:
--   Proof of Theorem 1, (31), p. 49 — if everyone else is truthful, j's expected payment is Σ_i Σ_y E(e_j(y)) Σ_x P_X(x)p_y(x) Σ_{y′} p_{y′}(x)q^{ij}_y(y′)
-- statement:
--   Consider the SRA game with a valid generating model $(P_X,\mathbf p)$, a legal allocation and legal choices of peers and of the pairs $j_1(i),j_2(i)$, and a fixed agent $j$ with $|\mathcal N_j|<N$. Suppose every agent other than $j$ reports truthfully on every task, and that $j$ uses stochastic reporting strategies $\mathbf q^{ij}$ on her tasks $i\in\mathcal N_j$. Write $\mathbb E(e_j(y))$ for the expected payment for answer $y$ under the truthful profile. Then agent $j$'s expected total payment is
--   $$\mathbb E[\tau_j]=\sum_{i\in\mathcal N_j}\sum_{y\in\mathcal Y}\mathbb E(e_j(y))\sum_{x\in\mathcal X}P_X(x)\,p_y(x)\sum_{y'\in\mathcal Y}p_{y'}(x)\,q^{ij}_y(y').$$
--
--   The summand of task $i$ is the paper's $R(\mathbf q^{ij})$ of (31): the peer observes and reports $y$, agent $j$ observes $y'$ and reports $y$, and the payment $e_j(y)$, being computed from tasks $j$ does not perform, is independent of both. The identity reduces the best-response problem to a linear program in $\mathbf q^{ij}$.
--
--   **Formalization Note** The left side is the expectation of $\tau_j$ computed as a finite sum over all types, observations and reports under the product law; it is not defined by this formula. The page writes $P(Y^i_{j'}=y,Y^i_j=y)$ and $\mathbb E(r_j(y))$; these are read as "the peer observes $y$ and $j$ reports $y$" and $\mathbb E(e_j(y))$, as the right-hand side of (31) shows. The total over $\mathcal N_j$ is the sum of the per-task rewards. $\mathbb E(e_j(y))$ is evaluated under the all-truthful profile, which is legitimate because it does not depend on $j$'s reports.
-- source:
--   Kamble, Shah, Marn, Parekh & Ramchandran, The Square Root Agreement Rule for Incentivizing Truthful Feedback on Online Platforms, arXiv:1507.07045v5, p. 49, proof of Theorem 1, eq. (31)

import Mathlib
import Definitions.Def_SqrtAgreement_SRA_Model

namespace SqrtAgreement.SRA

theorem payoff_decomposition {m k N M : ℕ} (G : GenModel m k) (K : ℝ) (S : Setting N M)
    (hG : G.Valid) (hS : S.Legal) (j : Fin M) (hN : (S.tasks j).card < N)
    (Q' : Profile N M k) (hQ' : IsDeviation S (symm (truthful k)) Q' j) :
    expPay G K S Q' j =
      ∑ i ∈ S.tasks j, ∑ y : Fin k, expE G K S (symm (truthful k)) j y *
        ∑ x : Fin m, G.PX x * G.p x y * ∑ y' : Fin k, G.p x y' * Q' i j y' y := by sorry

end SqrtAgreement.SRA
