-- Prove2me | Theorems.Thm_QueueBandit_QUCB_lemma_17
-- name    : QueueBandit.QUCB.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:40:32.079011+00:00
-- url     : https://prove2.me/theorems/769bed77-5bd1-47c7-b851-8cfd4b440fd6
-- title:
--   Lemma 17, p. 34 — refined regeneration bound: P[{B_u(t) > v_u(t)} ∩ ℰ₁ ∩ ℰ₂] ≤ 4/t³ + 2/t⁴
-- statement:
--   Throughout, $(\lambda,\mu)$ is an instance of the $U\times K$ switch satisfying Assumptions 1 and 2 (entries in $[0,1]$, unique optimal matching $k^*$, $\epsilon_u=\mu^*_u-\lambda_u>0$), $2\le K$ and $U\le K$, and $\mathbb P$ is the law of the system started from the stationary law $\pi_{(\lambda,\mu^*)}$ of Assumption 3. Run Q-UCB with any covering family and tie-breaking rules, fix $\beta>1$ and let $w(t)=t^{1-1/\beta}$,
--   $$v'_u(t)=\frac{6K}{\epsilon_u}w(t),\qquad v_u(t)=\frac{24\log t}{\epsilon_u^2}+\frac{60K}{\epsilon_u}\frac{v'_u(t)\log^2t}{t}.$$
--   Then for every $t$ with $w(t)/\log t\ge2/\epsilon_u$ and $v_u(t)+v'_u(t)\le t/2$,
--   $$\mathbb P\big[\{B_u(t)>v_u(t)\}\cap\mathcal E_1\cap\mathcal E_2\big]\ \le\ \frac4{t^3}+\frac2{t^4}.$$
--
--   So in the late stage the current regenerative cycle of queue $u$ has length at most $v_u(t)=O(\log t/\epsilon_u^2+K^2w(t)\log^2t/(\epsilon_u^2t))$ with high probability, which is what makes the queue-regret decay.
--
--   **Formalization Note** Here $v_u(t)$ is the real number above and $B_u(t)>v_u(t)$ is compared in $\mathbb R$.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 34, Lemma 17; proof p. 34, (23)–(25)

import Mathlib
import Definitions.Def_QueueBandit_QUCB_Model
import Definitions.Def_QueueBandit_QUCB_Algorithm1

namespace QueueBandit.QUCB

theorem lemma_17 {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (I : Instance U K)
    (A : QUCBRule U K) (β : ℝ) (hβ : 1 < β) (u : Fin U) (t : ℕ)
    (hw : 2 / I.eps u ≤ w β t / Real.log t) (hv : I.v β u t + I.vPrime β u t ≤ (t : ℝ) / 2) :
    I.P.real ({ω | I.v β u t < (A.B I u t ω : ℝ)} ∩ A.E1 I β t ∩ E2 β t) ≤
      4 / (t : ℝ) ^ 3 + 2 / (t : ℝ) ^ 4 := by sorry

end QueueBandit.QUCB
