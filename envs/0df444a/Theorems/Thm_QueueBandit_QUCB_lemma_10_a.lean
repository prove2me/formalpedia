-- Prove2me | Theorems.Thm_QueueBandit_QUCB_lemma_10_a
-- name    : QueueBandit.QUCB.lemma_10_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:55.437985+00:00
-- url     : https://prove2.me/theorems/ee9cee01-7f15-4f3d-8ea9-13f90cdd5db0
-- title:
--   Lemma 10(a), p. 24 — the number of explore slots in (t₁, t₂] exceeds 5 max(log t, K(log³ t₂ − log³ t₁)) with probability at most 1/t⁴
-- statement:
--   Let $\mathsf E(l)$ be the explore indicators of Q-UCB, independent Bernoulli variables with means $\min\{1,3K\log^2 l/l\}$. Throughout, $(\lambda,\mu)$ is an instance of the $U\times K$ switch satisfying Assumptions 1 and 2 (entries in $[0,1]$, unique optimal matching $k^*$, $\epsilon_u=\mu^*_u-\lambda_u>0$), $2\le K$ and $U\le K$, and $\mathbb P$ is the law of the system started from the stationary law $\pi_{(\lambda,\mu^*)}$ of Assumption 3. For all natural numbers $t\ge1$ and $1\le t_1<t_2$,
--   $$\mathbb P\Big[\sum_{l=t_1+1}^{t_2}\mathsf E(l)\ \ge\ 5\max\big(\log t,\ K(\log^3t_2-\log^3t_1)\big)\Big]\ \le\ \frac1{t^4}.$$
--
--   This is the high-probability bound on the forced exploration over a window, used in Lemmas 16 and 17 to control the explore slots inside the current regenerative cycle.
--
--   **Formalization Note** The hypotheses $t\ge1$ and $t_1\ge1$ are added: the page writes "for any $t$ and $t_1<t_2$", and at $t_1=0$ the paper's $\log^30=-\infty$ makes the claim trivial while Lean's $\log 0=0$ would not (paper.md slip 4). $\log^3x=(\log x)^3$.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 24, Lemma 10(a); proof p. 24, display (4), Chernoff bound (5)

import Mathlib
import Definitions.Def_QueueBandit_QUCB_Model
import Definitions.Def_QueueBandit_QUCB_Algorithm1

namespace QueueBandit.QUCB

theorem lemma_10_a {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (I : Instance U K)
    (t t₁ t₂ : ℕ) (ht : 1 ≤ t) (ht₁ : 1 ≤ t₁) (h₁₂ : t₁ < t₂) :
    I.P.real {ω : Ω U K | 5 * max (Real.log t) ((K : ℝ) * (Real.log t₂ ^ 3 - Real.log t₁ ^ 3)) ≤
        ((∑ l ∈ Finset.Ioc t₁ t₂, explore l ω : ℕ) : ℝ)} ≤ 1 / (t : ℝ) ^ 4 := by sorry

end QueueBandit.QUCB
