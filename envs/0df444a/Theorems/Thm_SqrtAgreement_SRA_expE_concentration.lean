-- Prove2me | Theorems.Thm_SqrtAgreement_SRA_expE_concentration
-- name    : SqrtAgreement.SRA.expE_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:42.594375+00:00
-- url     : https://prove2.me/theorems/a8c46450-e462-450f-bdcb-e9dad8bd7e34
-- title:
--   Proof of Theorem 1, (29)–(30), p. 49 — under truthful reporting |E(e_j(y)) − K/√g(y)| ≤ σ(N) → 0, uniformly given α, n, K
-- statement:
--   Fix $n\in\mathbb N$, $\alpha>0$ and $K>0$. Under the truthful strategy profile of the SRA game, the expected payment $\mathbb E(e_j(y))$ for an answer $y$ converges to $K/\sqrt{g(y)}$, where $g(y)=\sum_x P_X(x)p_y(x)^2$, uniformly: for every $\varepsilon>0$ there is $N_0$, depending only on $n,\alpha,K,\varepsilon$, such that for every finite answer set $\mathcal Y$, every valid $\alpha$-separated generating model $(P_X,\mathbf p)$, every number of tasks $N>N_0$, every population and legal allocation with $|\mathcal M_i|\ge2$ and $|\mathcal N_j|\le n$, every legal choice of pairs and peers, every agent $j$ and every $y\in\mathcal Y$,
--   $$\Big|\,\mathbb E(e_j(y))-\frac{K}{\sqrt{g(y)}}\,\Big|\ \le\ \varepsilon .$$
--
--   This is the statement $|\mathbb E(e_j(y))-K/\sqrt{g(y)}|\le\sigma(N)$ with $\sigma(N)\to 0$ depending only on $\alpha$, $n$ and $K$ and not on $y$; it is the quantitative heart of Theorems 1 and 2.
--
--   **Formalization Note** The page prints "$\sigma(N)=o(N)$"; the bound used is $\sigma(N)\to0$ ($o(1)$, as the proof of Theorem 2 writes), and the $\forall\varepsilon\,\exists N_0$ form states exactly that, uniformly. $N_0$ is chosen before the answer set, the model, the population, the allocation and the mechanism's choices, matching "depends only on $\alpha$, $n$ and $K$". The expectation is the finite sum under the all-truthful product law.
-- source:
--   Kamble, Shah, Marn, Parekh & Ramchandran, The Square Root Agreement Rule for Incentivizing Truthful Feedback on Online Platforms, arXiv:1507.07045v5, p. 49, proof of Theorem 1, eqs. (29)–(30) and the sentence after (30)

import Mathlib
import Definitions.Def_SqrtAgreement_SRA_Model

namespace SqrtAgreement.SRA

theorem expE_concentration (n : ℕ) (α K ε : ℝ) (hα : 0 < α) (hK : 0 < K) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ (k m : ℕ) (G : GenModel m k), G.Valid → G.AlphaSeparated α →
      ∀ (N M : ℕ), N0 < N → ∀ S : Setting N M, S.Valid n →
        ∀ (j : Fin M) (y : Fin k),
          |expE G K S (symm (truthful k)) j y - K / Real.sqrt (G.agree y)| ≤ ε := by sorry

end SqrtAgreement.SRA
