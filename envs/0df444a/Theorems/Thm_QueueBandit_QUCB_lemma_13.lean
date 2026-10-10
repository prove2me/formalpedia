-- Prove2me | Theorems.Thm_QueueBandit_QUCB_lemma_13
-- name    : QueueBandit.QUCB.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:40:24.184979+00:00
-- url     : https://prove2.me/theorems/46d4f475-e607-4fe5-b67b-307a3eae734e
-- title:
--   Lemma 13, p. 30 — P[{Q_u(l) > 2K w(t)} ∩ ℰ₁ ∩ ℰ₂] ≤ 1/t³ for every l ∈ [1, t] when w(t)/log t ≥ 2/ε_u
-- statement:
--   Throughout, $(\lambda,\mu)$ is an instance of the $U\times K$ switch satisfying Assumptions 1 and 2 (entries in $[0,1]$, unique optimal matching $k^*$, $\epsilon_u=\mu^*_u-\lambda_u>0$), $2\le K$ and $U\le K$, and $\mathbb P$ is the law of the system started from the stationary law $\pi_{(\lambda,\mu^*)}$ of Assumption 3. Run Q-UCB with any covering family and tie-breaking rules, fix $\beta>1$, $w(t)=t^{1-1/\beta}$, and let $\mathcal E_1$ be as in Lemma 11 and $\mathcal E_2=\{\sum_{l=1}^t\mathsf E(l)\le Kw(t)\}$. Then for every $t$ with $w(t)/\log t\ge 2/\epsilon_u$ and every $l\in[1,t]$,
--   $$\mathbb P\big[\{Q_u(l)>2Kw(t)\}\cap\mathcal E_1\cap\mathcal E_2\big]\ \le\ \frac1{t^3}.$$
--
--   This coarse bound on the queue length is the starting point of the recursive refinement of Lemmas 14, 16 and 17.
--
--   **Formalization Note** The proof uses that $Q^*_u(l)$ has the stationary law (Assumption 3), which is the geometric law of the `Model` module.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 30, Lemma 13; proof pp. 30–31

import Mathlib
import Definitions.Def_QueueBandit_QUCB_Model
import Definitions.Def_QueueBandit_QUCB_Algorithm1

namespace QueueBandit.QUCB

theorem lemma_13 {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (I : Instance U K)
    (A : QUCBRule U K) (β : ℝ) (hβ : 1 < β) (u : Fin U) (t l : ℕ) (hl₁ : 1 ≤ l) (hlt : l ≤ t)
    (hw : 2 / I.eps u ≤ w β t / Real.log t) :
    I.P.real ({ω | 2 * (K : ℝ) * w β t < (A.Q I u l ω : ℝ)} ∩ A.E1 I β t ∩ E2 β t) ≤
      1 / (t : ℝ) ^ 3 := by sorry

end QueueBandit.QUCB
