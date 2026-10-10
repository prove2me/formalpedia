-- Prove2me | Theorems.Thm_QueueBandit_QUCB_lemma_14
-- name    : QueueBandit.QUCB.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:40:26.927986+00:00
-- url     : https://prove2.me/theorems/ebb5f303-680d-4f3f-81c6-b763d49121e1
-- title:
--   Lemma 14, p. 31 — first-cut regeneration bound: P[{B_u(t − v_u(t)) > v′_u(t)} ∩ ℰ₁ ∩ ℰ₂] ≤ 2/t³
-- statement:
--   Throughout, $(\lambda,\mu)$ is an instance of the $U\times K$ switch satisfying Assumptions 1 and 2 (entries in $[0,1]$, unique optimal matching $k^*$, $\epsilon_u=\mu^*_u-\lambda_u>0$), $2\le K$ and $U\le K$, and $\mathbb P$ is the law of the system started from the stationary law $\pi_{(\lambda,\mu^*)}$ of Assumption 3. Run Q-UCB with any covering family and tie-breaking rules, fix $\beta>1$, let $w(t)=t^{1-1/\beta}$, $v'_u(t)=\frac{6K}{\epsilon_u}w(t)$, and let $v_u$ be an arbitrary function of $t$ with natural values. Then for every $t$ with $w(t)/\log t\ge2/\epsilon_u$ and $v_u(t)+v'_u(t)\le t/2$,
--   $$\mathbb P\big[\{B_u(t-v_u(t))>v'_u(t)\}\cap\mathcal E_1\cap\mathcal E_2\big]\ \le\ \frac2{t^3}.$$
--
--   In words: on the good events, queue $u$ has been empty within the last $v'_u(t)$ slots before time $t-v_u(t)$, except with probability $2/t^3$.
--
--   **Formalization Note** "Let $v_u$ be an arbitrary function": $v_u$ is taken natural-valued so that $t-v_u(t)$ is a time slot; the hypothesis $v_u(t)+v'_u(t)\le t/2$ guarantees that the natural subtraction does not truncate (paper.md slip 8). $B_u(\cdot)>v'_u(t)$ is compared in $\mathbb R$.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 31, Lemma 14; proof pp. 31–32, (17)–(19)

import Mathlib
import Definitions.Def_QueueBandit_QUCB_Model
import Definitions.Def_QueueBandit_QUCB_Algorithm1

namespace QueueBandit.QUCB

theorem lemma_14 {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (I : Instance U K)
    (A : QUCBRule U K) (β : ℝ) (hβ : 1 < β) (u : Fin U) (v : ℕ → ℕ) (t : ℕ)
    (hw : 2 / I.eps u ≤ w β t / Real.log t) (hv : (v t : ℝ) + I.vPrime β u t ≤ (t : ℝ) / 2) :
    I.P.real ({ω | I.vPrime β u t < (A.B I u (t - v t) ω : ℝ)} ∩ A.E1 I β t ∩ E2 β t) ≤
      2 / (t : ℝ) ^ 3 := by sorry

end QueueBandit.QUCB
