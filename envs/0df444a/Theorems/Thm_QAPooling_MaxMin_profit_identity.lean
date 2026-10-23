-- Prove2me | Theorems.Thm_QAPooling_MaxMin_profit_identity
-- name    : QAPooling.MaxMin.profit_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:30.046021+00:00
-- url     : https://prove2.me/theorems/da223a69-acc5-4786-8c26-bc533ad0d03e
-- title:
--   Proof of Theorem 4.1, pp. 14–15 — u(p*; j) = Σᵢ wᵢ D_G(p* ∥ pᵢ) + µⱼ
-- statement:
--   Let $s$ be a scoring rule with exposure function $g$, let $p_1,\dots,p_m\in\mathcal D$ with weights $w_i$ adding to $1$, and let $p^*\in\mathcal D$. Suppose that
--   $$g(p^*)=\sum_{i=1}^m w_i\,g(p_i)+\lambda\mathbf 1_n+\mu$$
--   for some $\lambda\in\mathbb R$ and $\mu\in\mathbb R^n$ with $\mu_j=0$ whenever $p^*_j>0$. Then for every outcome $j$, the agent's profit $u(p^*;j)=s(p^*;j)-\sum_i w_i s(p_i;j)$ satisfies
--   $$u(p^*;j)=\sum_{i=1}^m w_i\,D_G(p^*\,\|\,p_i)+\mu_j.$$
--
--   This is the computation at the heart of the proof of Theorem 4.1: the profit at the QA pool is the same weighted Bregman sum for every outcome, plus a non-negative correction $\mu_j$ that vanishes on the support of $p^*$.
--
--   **Formalization Note** The identity is algebraic: it needs neither properness nor $\mu\ge 0$, only Equation (2) at $p^*$ and at each $p_i$ and $\sum_i w_i=1$.
-- source:
--   Neyman & Roughgarden, From Proper Scoring Rules to Max-Min Optimal Forecast Aggregation, arXiv:2102.07081v2, pp. 14–15, proof of Theorem 4.1 (chain of equalities for u(p*; j))

import Mathlib
import Definitions.Def_QAPooling_MaxMin_Model

namespace QAPooling.MaxMin

/-- The profit identity in the proof of Theorem 4.1 (pp. 14–15): if `p* ∈ D` and
`g(p*) = Σ_i w_i g(p_i) + λ 1_n + μ` with `μ_j = 0` whenever `p*_j > 0`, then for every outcome `j`,
`u(p*; j) = Σ_i w_i D_G(p* ∥ p_i) + μ_j`. -/
theorem profit_identity {n m : ℕ} (s : ScoringRule n) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hg : IsExposure s g)
    (p : Fin m → Fin n → ℝ) (hp : ∀ i, p i ∈ forecastDomain s)
    (w : Fin m → ℝ) (hw1 : ∑ i, w i = 1)
    (pstar : Fin n → ℝ) (hD : pstar ∈ forecastDomain s)
    (lam : ℝ) (mu : Fin n → ℝ)
    (hkkt : ∀ j, g pstar j = ∑ i, w i * g (p i) j + lam + mu j)
    (hcs : ∀ j, 0 < pstar j → mu j = 0) :
    ∀ j, profit s p w pstar j = ((∑ i, w i * bregman s g pstar (p i) + mu j : ℝ) : EReal) := by sorry

end QAPooling.MaxMin
